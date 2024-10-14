import Lean.Elab.Command
import Lean.Elab.Inductive
import Lean.Server.Utils



namespace cvc5.Autogen

open Lean
open Elab
open Command (CommandElab CommandElabM)



abbrev StringSet := Lean.RBTree String compare

namespace StringSet
def empty : StringSet := Lean.RBTree.empty
end StringSet

abbrev Doc := Array Substring

def Doc.get (doc : Doc) : String :=
  ""
  |> doc.foldl fun s line =>
    if s.isEmpty
    then line.toString
    else s!"{s}\n{line}"

structure Variant where
  doc? : Option Doc
  name : Name
  offset : Option Int
  ifdef : Option String

namespace Variant
def ctorView (self : Variant) (ty : Name) : CommandElabM Command.CtorView :=
  let ident := mkIdent self.name
  return {
    ref := ← `($ident)
    modifiers := { docString? := self.doc?.map Doc.get }
    declName := ty.append self.name
    binders := Syntax.missing
    type? := none
  }
end Variant

structure Enum where
  doc : Doc
  name : Name
  variants : Array Variant

namespace Enum
def inductiveView (self : Enum) (ns : Name) : CommandElabM Command.InductiveView := do
  let ident := mkIdent self.name
  return {
    ref := ← `(inductive $ident)
    declId := ← `($ident)
    modifiers := { docString? := self.doc.get }
    shortDeclName := self.name
    declName := ns.append self.name
    levelNames := []
    binders := Lean.Syntax.missing
    type? := none
    ctors := ← self.variants.filterMapM fun v =>
      if v.ifdef.isNone then
        v.ctorView (ns.append self.name)
      else return none
    derivingClasses := #[]
    computedFields := #[]
  }

protected def toString : Enum → String
| ⟨doc, name, variants⟩ => Id.run do
  let mut s := "/**"
  for line in doc do
    s := s!"{s}\n * {line}"
  s := s ++ "\n */\n" ++ "enum ENUM(" ++ name.toString ++ ") : int32_t {"
  for variant in variants do
    if let some doc := variant.doc? then
      s := s ++ "\n  /**"
      for line in doc do
        s := s!"{s}\n   * {line}"
      s := s ++ "\n   */"
    s := s ++ s!"\n  EVALUE({variant.name}"
    if let some offset := variant.offset then
      s := s ++ s!" = {offset}"
    s := s ++ "),"
  s := s ++ "\n}"
  return s

protected def toLeanString : Enum → String
| ⟨doc, name, variants⟩ => Id.run do
  let mut s := "/--"
  for line in doc do
    s := s!"{s}\n{line}"
  s := s ++ "\n-/\n" ++ "inductive " ++ name.toString
  for variant in variants do
    if let some doc := variant.doc? then
      s := s ++ "\n  /--"
      for line in doc do
        s := s!"{s}\n   {line}"
      s := s ++ "\n  -/"
    s := s ++ s!"\n| {variant.name}"
  return s

instance : ToString Enum := ⟨Enum.toString⟩
end Enum



abbrev ParserT (m : Type → Type := IO) (α : Type) :=
  StateT Substring m α

abbrev Parser (α : Type) :=
  ParserT Id α

variable [Monad m] [MonadLiftT IO m]

instance : MonadLift Parser (ParserT m) where
  monadLift parse txt := do
    let res := parse txt
    return res

@[inline]
private
def isNewline : Char → Bool
| '\n' | '\r' => true
| _ => false

@[inline]
private
def currLine (s : Substring) :=
  s.takeWhile (¬ isNewline ·)

namespace ParserT

def runSub (code : ParserT m α) (txt : Substring) (total := false) : m α := do
  let (res, rest) ← code txt
  if ¬ total ∨ rest.isEmpty then
    return res
  else
    IO.throwServerError s!"parsing stopped with remaining input\n\n```\n{rest}\n```\n"

def run (code : ParserT m α) (txt : String) (total := false) : m α := do
  code.runSub txt.toSubstring total

end ParserT



namespace Parser
export ParserT (runSub run)

@[inline]
def rest : Parser Substring :=
  fun s => (s, s)

/-- Extracts `n` lines if `0 < n`, extracts all lines otherwise. -/
partial def nextLines (n? : Option Nat := none) : ParserT m (Array Substring) :=
  fun txt => do
    let res ← aux n? #[] |>.runSub txt
    return (res, txt)
where aux n? (acc : Array Substring) : ParserT m (Array Substring) := fun txt => do
  match (txt.isEmpty, n?) with
  | (false, none)
  | (false, some (_ + 1)) =>
    let line := txt.takeWhile (¬ isNewline ·)
    let n? := n?.map Nat.pred
    let acc := acc.push line
    let txt := txt.extract ⟨line.bsize.succ⟩ ⟨txt.bsize⟩
    aux n? acc txt
  | (true, _)
  | (_, some 0) => return (acc, txt)

def lineTail : ParserT m Substring := fun s =>
  let line := s.takeWhile (¬ isNewline ·)
  let s := s.extract ⟨line.bsize.succ⟩ ⟨s.bsize⟩
  return (line, s)

@[always_inline]
def isEoi : ParserT m Bool :=
  fun s => return (s.isEmpty, s)

def fail (msg : String) : ParserT m α := do
  if ← isEoi then
    IO.throwServerError s!"{msg}\n- parser at EOI"
  else
    let lines ← nextLines (some 5)
    (msg ++ "\n- parser at")
    |> lines.foldl (fun msg line => msg ++ "\n  | " ++ line.toString)
    |> IO.throwServerError

@[always_inline]
def ws : ParserT m Unit :=
  fun s => return ((), s.trimLeft)

def pos : ParserT m String.Pos :=
  fun s => return (s.startPos, s)

@[always_inline]
def skipChar (n := 1) : ParserT m Unit :=
  fun s => return ((), (s.drop n))

@[always_inline]
def skipWhile (f : Char → Bool) : ParserT m Unit :=
  fun s =>
    return ((), (s.dropWhile f))

def tryIdent : ParserT m (Option Substring) := fun txt =>
  if txt.isEmpty then
    return (none, txt)
  else
    let c := txt.get ⟨0⟩
    if c.isAlpha || c = '_' then
      let ident := txt.takeWhile fun c => c.isAlphanum || c = '_'
      let txt := txt.drop ident.bsize
      return (ident, txt)
    else
      return (none, txt)

def ident! : ParserT m Substring := do
  let some ident ← tryIdent
    | fail "expected identifier"
  return ident

section tag
variable
  (tag : String) (andThen : Substring → Bool := fun _ => true)

def tryTag : ParserT m Bool :=
  fun txt => do
    let tag := tag.toSubstring
    if tag == txt.extract 0 ⟨tag.bsize⟩ then
      let txt := txt.extract ⟨tag.bsize⟩ ⟨txt.bsize⟩
      if andThen txt then
        return (true, txt)
    return (false, txt)

def peek : ParserT m Bool := fun txt => do
  let (b, _) ← tryTag tag andThen txt
  return (b, txt)

def tag? : ParserT m Unit := do
  let _ ← tryTag tag andThen

def tag! : ParserT m Unit := do
  if ¬ (← tryTag tag andThen) then
    fail s!"expected tag `{tag}`"

partial def skipToTag (tag : String) : ParserT m Bool := do
  if ← isEoi then
    return false
  else if ← tryTag tag then
    return true
  else
    skipChar
    let c := tag.get ⟨0⟩
    skipWhile (· ≠ c)
    skipToTag tag

def tags! (tags : Array String) (sep : ParserT m Unit := ws) : ParserT m Unit :=
  aux 0
where aux idx : ParserT m Unit := do
  if h : idx < tags.size then
    if 0 < idx then
      sep
    let tag := tags.get ⟨idx, h⟩
    tag! tag
    aux idx.succ
end tag

partial def wsCmt : ParserT m Unit := do
  let oldPos ← pos
  ws
  if ← tryTag "//" then
    let _ ← lineTail
  let newPos ← pos
  if oldPos ≠ newPos then wsCmt

def tryNat : ParserT m (Option Nat) := fun txt =>
  if txt.isEmpty then
    return (none, txt)
  else
    let s := txt.takeWhile Char.isDigit
    if s.isEmpty then
      return (none, txt)
    else
      let txt := txt.extract ⟨s.bsize⟩ ⟨txt.bsize⟩
      if let some n := s.toString.toNat? then
        return (n, txt)
      else
        fail s!"illegal `Nat` value `{s}`" txt

def nat! : ParserT m Nat := do
  if let some n ← tryNat then
    return n
  else
    fail "expected `Nat` value"

def tryInt : ParserT m (Option Int) := do
  let neg ← tryTag "-"
  if neg then
    ws
  let some n ← tryNat
    | return none
  if neg then
    return Int.negOfNat n
  else
    return Int.ofNat n

def int! : ParserT m Int := do
  if let some i ← tryInt then
    return i
  else
    fail "expected `Int` value"

partial def tryDoc : ParserT m (Option Doc) := do
  if ← tryTag "/**" then
    aux #[]
  else return none
where aux (acc : Doc) : ParserT m Doc := do
  ws
  if ← isEoi then
    fail "reached EOI while parsing documentation"
  else if ← tryTag "*/" then
    return acc
  let _ ← tag? "*"
  let line ← Substring.trim <$> lineTail
  -- separator's end `*/` at the end of this line?
  if line.takeRight 2 == "*/".toSubstring then
    let line := line.dropRight 2 |>.trimRight
    return acc.push line
  else
    aux (acc.push line)

@[inline]
def doc! : ParserT m Doc := do
  if let some doc ← tryDoc then
    return doc
  else fail "expected documentation `/** ... */`"

partial def skipToDoc : ParserT m (Option Doc) := do
  if ← isEoi then
    return none
  else if let some doc ← tryDoc then
    return doc
  else
    skipChar
    skipToDoc

def tryVariant (ifdef : Option String) (doc? : Option Doc) : ParserT m (Option Variant) := do
  if ← tryTag "EVALUE" then
    ws
    tag! "("
    ws
    let name ← ident!
    let name := Name.mkSimple name.toString
    ws
    let offset ←
      if ← tryTag "=" then
        ws
        let i ← int!
        pure (some i)
      else pure none
    ws
    tag! ")"
    ws
    let _ ← tryTag ","
    return some { doc?, name, offset, ifdef }
  else return none

def variant! (ifdef : Option String) (doc? : Option Doc) : ParserT m Variant := do
  if let some v ← tryVariant ifdef doc? then
    return v
  else
    fail "expected variant definition"


partial def variants : ParserT m (Array Variant) :=
  aux [] #[]
where
  ignoreSep : ParserT m Unit := do
    if ← tryTag "/*" (fun s => s.get ⟨0⟩ ≠ '*') then
      skipToTag "*/" >>= fun _ => wsCmt
  aux (ifdef : List String) (acc : Array Variant) : ParserT m (Array Variant) := do
    wsCmt
    ignoreSep
    -- closing `}`?
    if ← peek "}" then
      return acc

    if ← tryTag "#ifdef" then
      ws
      let id ← ident!
      aux (id.toString :: ifdef) acc
    else if ← tryTag "#endif" then
      let _ :: tail := ifdef
        | fail "found `#endif` while not being in a `#ifdef`"
      aux tail acc
    else
      let doc? ← tryDoc
      wsCmt
      let variant ← variant! ifdef.head? doc?
      let acc := acc.push variant
      aux ifdef acc

def tryEnum : ParserT m (Enum ⊕ Bool) := do
  let some doc ← skipToDoc
    | return .inr true
  ws
  if ← tryTag "enum" then
    ws
    tags! #["ENUM", "("]
    let name ← ident!
    let name := Name.mkSimple name.toString
    ws
    tags! #[")"]
    ws
    if ¬ (← tryTag "{") then
      ws
      tags! #[":"]
      ws
      let _ ← tryTag "u"
      tags! #["int32_t", "{"]
    ws
    let variants ← variants
    tag! "}"
    return .inl {doc, name, variants}
  else
    return .inr false

partial def enums : ParserT m (Array Enum) := do
  aux #[]
where aux (acc : Array Enum) : ParserT m (Array Enum) := do
  match ← tryEnum with
  | .inl enum => aux (acc.push enum)
  | .inr false => aux acc
  | .inr true => return acc

def ignoreHeader : ParserT m Unit := do
  if ← tryTag "/***" then
    let _ ← skipToTag "*/"

def parseEnums (txt : String) : m (Array Enum) := do
  ParserT.run
    (do
      ignoreHeader
      enums)
    txt
end Parser



/-- Loads C++ enum definitions from a file as Lean enums. -/
syntax (name := cppEnumsToLean) "cppEnumsToLean!"
  ( "(" "ignore" ident+ ")" )?
  str
: command

private def cvc5Dir :=
  let os :=
    if System.Platform.isWindows then "Win64"
    else if System.Platform.isOSX then "macOS"
    else "Linux"
  let arch :=
    if System.Platform.target.startsWith "x86_64"
    then "x86_64" else "arm64"
  s!"cvc5-{os}-{arch}-static"

@[inherit_doc cppEnumsToLean, command_elab cppEnumsToLean]
unsafe def cppEnumsToLeanImpl : CommandElab
| `(command|
  cppEnumsToLean!
    $[ (ignore $[ $ignoreIds:ident ]*) ]?
    $file
) => do
  let mut ignored := StringSet.empty
  if let some ignoreIds := ignoreIds then
    for ignoreId in ignoreIds do
      ignored := ignored.insert ignoreId.getId.toString
  let file := file.getString
  let path := ".lake/" ++ cvc5Dir ++ "/include/cvc5/" ++ file
  -- let currDir ← IO.currentDir
  -- println! "currDirr = `{currDir}`"
  -- println! "path = `{path}`"
  let content ← IO.FS.readFile path
  let enums ← Parser.parseEnums content
  let ns ← getCurrNamespace
  -- println! "parsed {enums.size} enum(s)"
  for enum in enums do
    if ignored.contains enum.name.toString then
      -- println! "ignoring {enum.name}"
      continue
    let enumName := ns.append enum.name
    -- println! "generating for {enumName}"
    -- println! "```\n{enum.toLeanString}\n```"

    let view ← enum.inductiveView ns
    Command.elabInductiveViews #[view]

    let enumIdent := mkIdent enumName
    let stx ← `(deriving instance Inhabited, DecidableEq, Repr, Hashable for $enumIdent)
    elabDeriving stx
| _ => throwUnsupportedSyntax

-- cppEnumsToLean! "cvc5_kind.h"

-- #check Kind
-- #check (inferInstance : BEq Kind)
-- #check (inferInstance : Hashable Kind)
-- #check (inferInstance : Inhabited Kind)

-- #check cvc5.Internal.Kind.INTERNAL_KIND
-- #check SortKind
-- #check SortKind.BAG_SORT
-- #check (inferInstance : BEq SortKind)
-- #check (inferInstance : Hashable SortKind)
-- #check (inferInstance : Inhabited SortKind)
