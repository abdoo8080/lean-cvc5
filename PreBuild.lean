import Lean.Data.Position
import Std.Internal.Parsec

namespace cvc5.PreBuild

open Std.Internal (Parsec)
open Std.Internal.Parsec (ParseResult Input)

/-- `C++` docstring as lines.

Does not feature the line-leading `*` featured in most `C++` docstrings. -/
abbrev Doc := Array String

/-- A variant in a `C++` enum. -/
structure Variant where
  doc? : Option Doc
  ident : String
  offset : Option Int
  ifdef : Option String

abbrev Variants := Array Variant

/-- A `C++` enum. -/
structure Enum where
  doc : Doc
  ident : String
  variants : Variants

/-- Lowercases the first letter of `ident`. -/
def Enum.toExternPref (e : Enum) :=
  e.ident.get 0
  |>.toLower
  |> e.ident.set 0

abbrev Enums := Array Enum

/-! ## Lean code generation -/

section codegen
open IO.FS (Handle)

variable (h : Handle) (pref : String)

def writeln (bits : List String) := do
  if ¬ bits.isEmpty then
    h.putStr pref
    for bit in bits do
      h.putStr bit
  h.putStrLn ""

def writelns (bbits : List (List String)) := do
  for bits in bbits do
    writeln h pref bits

def Doc.writeToLean (doc : Doc) : IO Unit := do
  let wln := writeln h pref
  wln ["/--"]
  for line in doc do
    wln [line]
  wln ["-/"]
  h.flush

def Variant.writeToLean (v : Variant) : IO Unit := do
  if let some doc := v.doc? then
    doc.writeToLean h pref
  writeln h pref ["| ", v.ident]

def Enum.writeToLean (e : Enum) (skipIfDefs := true) : IO Unit := do
  let wln := writeln h pref
  let wlns := writelns h pref
  -- write the type's doc
  e.doc.writeToLean h pref
  -- type definition
  wln ["inductive ", e.ident, " where"]
  -- write each variant (and its doc), populate `listAll`'s definition
  for v in e.variants do
    -- ignore variants inside `#ifdef`?
    if skipIfDefs ∧ v.ifdef.isSome then continue
    -- write variant as part of the type's definition
    v.writeToLean h (pref ++ "  ")
  wlns [
    ["deriving Inhabited, Repr, BEq, DecidableEq"],
    -- [],
    -- ["namespace ", e.ident],
    -- [],
    -- ["/-- Produces a string representation. -/"],
    -- ["@[extern \"", e.toExternPref, "_toString\"]"],
    -- ["protected opaque toString : ", e.ident, " → String"],
    -- [],
    -- ["instance : ToString ", e.ident, " := ⟨", e.ident, ".toString⟩"],
    -- [],
    -- ["/-- Produces a hash. -/"],
    -- ["@[extern \"", e.toExternPref, "_hash\"]"],
    -- ["protected opaque hash : ", e.ident, " → UInt64"],
    -- [],
    -- ["instance : Hashable ", e.ident, " := ⟨", e.ident, ".hash⟩"],
    -- [],
    -- ["end ", e.ident],
  ]

def Enums.writeToLean (es : Enums) (skipIfDefs := true) : IO Unit := do
  let wln := writeln h pref
  wln ["\
/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Adrien Champion
-/\
  "]
  wln []
  wln ["namespace cvc5"]
  for e in es do
    wln []
    e.writeToLean h pref skipIfDefs

def Enums.writeToFile (path : System.FilePath) (es : Enums) (skipIfDefs := true) : IO Unit := do
  let handle ← Handle.mk path .write
  es.writeToLean handle "" skipIfDefs

end codegen

/-- Parser monad, based on `Std.Internal.Parsec` over `String`s (actually `String.Iterator`). -/
abbrev Parser := @Std.Internal.Parsec.String.Parser

namespace Parser

section
open Std.Internal (Parsec)

/-! ## Exports from `Parsec` -/

abbrev fail : String → Parser α :=
  Parsec.fail
abbrev eof : Parser Unit :=
  Parsec.eof
abbrev isEof : Parser Bool :=
  Parsec.isEof
abbrev any : Parser Char :=
  Parsec.any
abbrev satisfy : (Char → Bool) → Parser Char :=
  Parsec.satisfy
abbrev notFollowedBy : Parser α → Parser Unit :=
  Parsec.notFollowedBy
abbrev peek? : Parser (Option Char) :=
  Parsec.peek?
abbrev skip : Parser Unit :=
  Parsec.skip
abbrev attempt : Parser α → Parser α :=
  Parsec.attempt
abbrev manyChars : Parser Char → Parser String :=
  Parsec.manyChars
abbrev many1Chars : Parser Char → Parser String :=
  Parsec.many1Chars

/-! ## Exports from `Parsec.String` -/

abbrev pstring : String → Parser String :=
  Parsec.String.pstring
abbrev skipString : String → Parser Unit :=
  Parsec.String.skipString
abbrev pchar : Char → Parser Char :=
  Parsec.String.pchar
abbrev skipChar : Char → Parser Unit :=
  Parsec.String.skipChar
abbrev digit : Parser Char :=
  Parsec.String.digit
abbrev digits : Parser Nat :=
  Parsec.String.digits
abbrev ws : Parser Unit :=
  Parsec.String.ws
end

/-! ## Helpers -/

def ptry (p : Parser α) : Parser (Option α) := do
  (some <$> attempt p) <|> (pure none)

def pchar? := (ptry $ pchar ·)
def pstring? := (ptry $ pstring ·)

def ptest (p : Parser α) : Parser Bool := do
  Option.isSome <$> ptry p

def pite (c : Parser Bool) (t e : Parser α) : Parser α := do
  if ← c then t else e

partial def skipUntil (p : Parser α) : Parser (Option α) := do
  if ← isEof then return none else
    if let some a ← ptry p then
      return a
    else
      skip
      skipUntil p

partial def takeUntil' (p : Parser α) (acc := "") : Parser (String × Option α) := do
  if ← isEof then return (acc, none) else
    if let some a ← ptry p then
      return (acc, some a)
    else
      let next ← any
      let acc := acc.push next
      takeUntil' p acc

def takeUntil (p : Parser α) (acc := "") : Parser String := do
  Prod.fst <$> takeUntil' (discard p) acc

def newline : Parser Char :=
  pchar '\n' <|> pchar '\r'

def lineTail (trimRight := true) : Parser String := do
  let tail ← takeUntil newline
  return if trimRight then tail.trimRight else tail

/-! ## Non-doc comments -/

def cmt.sl : Parser Unit := do
  discard $ pstring "//"
  if let some '/' ← peek? then
    fail "expected `//`-comment, found `///`-docstring"
  discard <| skipUntil newline

partial def cmt.ml : Parser Unit := do
  discard $ pstring "/*"
  if let some '*' ← peek? then
    fail "expected `/*...*/`-comment, found `/**...*/`-docstring"
  -- notFollowedBy $ pchar '*'
  closeOrNested 1
where closeOrNested : Nat → Parser Unit
  | 0 => return ()
  | n@(nPrev + 1) => do
    if ← ptest <| pstring "/*" then
      closeOrNested n.succ
    else if ← ptest <| pstring "*/" then
      closeOrNested nPrev
    else
      discard skip
      closeOrNested n

def header : Parser Unit := do
  discard $ pstring "/***"
  cmt.ml.closeOrNested 1

def cmt : Parser Unit :=
  cmt.ml <|> cmt.sl

partial def wsCmt : Parser Unit := do
  ws
  if ← ptest cmt then
    wsCmt
  else
    return ()

/-! ## Doc comments -/

partial def docCmtLines.ml (acc : Array String := #[]) : Parser Doc := do
  discard $ pstring "/**"
  parseLines acc
where
  docLineEnd : Parser Bool := do
    ( (fun _ => false) <$> newline ) <|> ( (fun _ => true) <$> pstring "*/" )
  parseLines (acc : Array String) : Parser Doc := do
    ws
    if ← ptest <| pstring "*/" then
      return acc
    if ← ptest <| pchar '*' then
      discard $ pchar? ' '
    let (line, closed) ← takeUntil' docLineEnd
    let acc := acc.push line
    if let some false := closed
    then parseLines acc
    else return acc

def pdoc : Parser Doc := docCmtLines.ml
def pdoc? := ptry pdoc

-- def skipToDoc : Parser (Option Doc) := do
--   skipUntil pdoc

/-! ## Delimiters -/

inductive Delim
| paren | brace | brack
deriving BEq, DecidableEq

def Delim.chars : Delim → Char × Char
| .paren => ('(', ')')
| .brace => ('{', '}')
| .brack => ('[', ']')

def delimited (p : Parser α) (delim : Delim := .paren) : Parser α := do
  let (op, cl) := delim.chars
  discard $ pchar op
  wsCmt
  let res ← p
  wsCmt
  discard $ pchar cl
  return res

def Delim.parse (d : Delim) : Parser α → Parser α :=
  delimited (delim := d)

/-! ## Identifiers -/

def pident.headChar : Parser Char :=
  satisfy fun c => c.isAlpha || c = '_'

def pident.tailChar : Parser Char :=
  headChar <|> satisfy Char.isDigit

def pident : Parser String := do
  let head ← pident.headChar
  let tail ← manyChars pident.tailChar
  return head.toString ++ tail

/-! ## Values -/

def pnat : Parser Nat :=
  digits

def pint : Parser Int := do
  let neg ← ptest $ pchar '-'
  if neg then wsCmt
  let n ← pnat
  return if neg then n else -n

/-! ## Variants -/

def pvariant (ifdef? : Option String) : Parser Variant := do
  let doc? ← pdoc?
  wsCmt
  discard $ pstring "EVALUE"
  wsCmt
  let (ident, offset1?) ←
    delimited do
      let ident ← pident
      wsCmt
      let offset? ←
        if ← ptest $ pchar '=' then
          wsCmt
          let i ← pint
          pure (some i)
        else pure none
      wsCmt
      pure (ident, offset?)
  wsCmt
  let offset2? ←
    if ← ptest $ pchar '=' then
      wsCmt
      let i ← pint
      pure (some i)
    else pure none
  wsCmt
  let offset? ←
    match (offset1?, offset2?) with
    | (none, o?)| (o?, none) => pure o?
    | (some o1, some o2) =>
      if o1 = o2 then pure <| some o1
      else fail s!"variant `{ident}` has two incompatible offsets: `{o1}` / `{o2}`"
  discard $ pchar? ','
  return ⟨doc?, ident, offset?, ifdef?⟩

partial def pvariants : Parser Variants := do
  loop 0 #[] none
where loop (i : Nat) (acc : Variants) (ifdef? : Option String) : Parser Variants := do
  wsCmt
  if let some '}' ← peek? then
    if let some ident := ifdef? then
      fail s!"found enum-closing `}`, but currently inside `#ifdef {ident}`"
    return acc
  else if ← ptest $ pstring "#ifdef" then
    wsCmt
    let ident ← pident
    if let some ident' := ifdef? then
      fail s!"found `#ifdef {ident}`, but currently inside `#ifdef {ident'}`"
    loop i acc ident
  else if ← ptest $ pstring "#endif" then
    if ifdef?.isNone then
      fail s!"found `#endif`, but currently not inside an `#ifdef`"
    loop i acc none
  else if ← isEof then
    return acc
  else
    let variant ← pvariant ifdef?
    let acc := acc.push variant
    loop i.succ acc ifdef?

partial def penumHead : Parser (Doc × String) := do
  wsCmt
  let doc ← pdoc
  wsCmt
  discard $ pstring "enum"
  wsCmt
  discard $ pstring "ENUM"
  wsCmt
  let ident ← delimited pident
  wsCmt
  return (doc, ident)

partial def penumTail (doc : Doc) (ident : String) : Parser Enum := do
  if ← ptest $ pchar ':' then
    wsCmt
    discard $ pchar? 'u'
    discard $ pstring "int32_t"
    wsCmt
  let variants ← delimited (delim := .brace) pvariants
  wsCmt
  discard $ pchar? ';'
  return ⟨doc, ident, variants⟩

partial def penums (acc : Enums := #[]) : Parser Enums := do
  if let some (doc, ident) ← skipUntil penumHead then
    let enum ← penumTail doc ident
    acc.push enum |> penums
  else return acc

def pfile : Parser Enums := do
  discard $ ptry header
  let enums ← penums
  wsCmt
  if ← isEof then return enums
  else fail s!"parsed {enums.size} enum(s), but there is some text left"

def prettyError
  (ι : String.Iterator) (content : String) (msg : String)
: IO String := do
  let pos := Parsec.Input.pos ι
  let map := content.toFileMap
  let position := map.toPosition pos
  let char := content.get? pos
  let charStr := match char with
  | none => "'<eof>'"
  | '\n' | '\r' => "'<newline>'"
  | some c => s!"'{c}'"

  let getLine (n : Nat) : Substring :=
    let startPos := map.positions[n]!
    let endPos := map.positions[n.succ]!
    content.toSubstring.extract startPos endPos |>.trimRight
  let line := position.line - 1
  let padding := toString position.line.succ |>.length
  let lpad (line? : Option Nat) : String :=
    let s := line?.map toString |>.getD ""
    ⟨s.data.leftpad padding ' '⟩

  return (
    s!"error at {position.line}-{position.column} on character {charStr}"
  ) ++ "\n" ++ (
    if 0 < line
    then s!" {lpad position.line.pred} | {getLine line.pred}"
    else s!" {lpad none} |"
  ) ++ "\n" ++ (
    s!"<{lpad position.line}>| {getLine line}"
  ) ++ "\n" ++ (
    if line.succ.succ < map.positions.size then
      s!" {lpad position.line.succ} | {getLine line.succ}"
    else
      s!" {lpad none} |"
  ) ++ "\n" ++ (
    s!"{msg}"
  )

def presentError (ι : String.Iterator) (content : String) (msg : String) : IO Lean.Position := do
  let pos := Parsec.Input.pos ι
  let map := content.toFileMap
  let position := map.toPosition pos
  let char := content.get? pos
  let charStr := match char with
  | none => "'<eof>'"
  | '\n' | '\r' => "'<newline>'"
  | some c => s!"'{c}'"
  IO.eprintln s!"error at {position.line}-{position.column} on character {charStr}"
  let getLine (n : Nat) : Substring :=
    let startPos := map.positions[n]!
    let endPos := map.positions[n.succ]!
    content.toSubstring.extract startPos endPos |>.trimRight
  let line := position.line - 1
  let padding := toString position.line.succ |>.length
  let lpad (line? : Option Nat) : String :=
    let s := line?.map toString |>.getD ""
    ⟨s.data.leftpad padding ' '⟩
  if 0 < line then
    IO.eprintln s!" {lpad position.line.pred} | {getLine line.pred}"
  else
    IO.eprintln s!" {lpad none} |"
  IO.eprintln s!"<{lpad position.line}>| {getLine line}"
  if line.succ.succ < map.positions.size then
    IO.eprintln s!" {lpad position.line.succ} | {getLine line.succ}"
  else
    IO.eprintln s!" {lpad none} |"
  IO.eprintln s!"{msg}"
  return position

def parseContentWith (p : Parser α) (content : String) (notEoiFail := true) : IO α :=
  let p : Parser α :=
    if notEoiFail then do
      let res ← p
      Parsec.eof
      return res
    else p
  match p content.iter with
  | .success _ a => return a
  | .error ι msg => do
    let pretty ← prettyError ι content msg
    throw <| IO.Error.userError pretty

def parseContent : String → IO Enums :=
  parseContentWith (notEoiFail := true) pfile

def parseFile (path : System.FilePath) : IO Enums :=
  IO.FS.readFile path >>= parseContent

end Parser

namespace Fs

abbrev FilePath := System.FilePath

abbrev Time := IO.FS.SystemTime

def writeLean (cpp lean :  FilePath) : IO Unit := do
  let enums ← Parser.parseFile cpp
  enums.writeToFile lean

/-! ## File writing and date-checking -/

namespace FilePath

def modified (p : FilePath) : IO Time := do
  let metadata ← p.metadata
  return metadata.modified

end FilePath

def updateLeanFile (cpp lean : FilePath) : IO Unit := do
  println! "- {cpp} → {lean}"
  println! "  updating"
  writeLean cpp lean
  println! "  done"

def updateLean (cppDir leanDir : FilePath) : IO Unit := do
  let pairs := [
    ("cvc5_kind.h", "Kind.lean"),
    ("cvc5_proof_rule.h", "ProofRule.lean"),
    ("cvc5_skolem_id.h", "SkolemId.lean"),
    ("cvc5_types.h", "Types.lean"),
  ]
  for (cpp, lean) in pairs do
    updateLeanFile (cppDir / cpp) (leanDir / lean)

end Fs

end cvc5.PreBuild

def fail (s : String) : IO α :=
  throw (.userError s)

open cvc5.PreBuild.Fs in
def main (args : List String) : IO Unit := do
  let (cppDir, leanDir) ← match args with
    | [cpp, lean] => pure ((cpp, lean) : FilePath × FilePath)
    | l => fail s!"expected exactly 2 arguments, found {l.length}"
  if ¬ (← cppDir.isDir) then
    fail s!"C++ directory `{cppDir}` does not exist or is not a directory"
  if ¬ (← leanDir.isDir) then
    fail s!"Lean directory `{leanDir}` does not exist or is not a directory"
  println! "updating enums `{cppDir}` → `{leanDir}`"
  updateLean cppDir leanDir
