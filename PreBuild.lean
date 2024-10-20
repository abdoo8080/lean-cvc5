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
  |>.toUpper
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
  e.doc.writeToLean h pref
  wln ["inductive ", e.ident]
  for v in e.variants do
    if skipIfDefs ∧ v.ifdef.isSome then
      continue
    v.writeToLean h pref
  wlns [
    ["deriving Inhabited, Repr, BEq, Hashable"],
    [],
    ["namespace ", e.ident],
    [],
    ["/-- Produces a string representation. -/"],
    ["@[extern \"", e.toExternPref, "_toString\"]"],
    ["protected opaque toString : ", e.ident, " → String"],
    [],
    ["instance : ToString ", e.ident, " := ⟨", e.ident, ".toString⟩"],
    [],
    ["end ", e.ident],
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
  wln []
  for e in es do
    e.writeToLean h pref skipIfDefs
    wln []

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

def trash (p : Parser α) : Parser Unit :=
  (fun _ => ()) <$> p

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
  Prod.fst <$> takeUntil' (trash p) acc

def newline : Parser Char :=
  pchar '\n' <|> pchar '\r'

def lineTail (trimRight := true) : Parser String := do
  let tail ← takeUntil newline
  return if trimRight then tail.trimRight else tail

/-! ## Non-doc comments -/

def cmt.sl : Parser Unit := do
  trash $ pstring "//"
  if let some '/' ← peek? then
    fail "expected `//`-comment, found `///`-docstring"
  trash <| skipUntil newline

partial def cmt.ml : Parser Unit := do
  trash $ pstring "/*"
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
      trash skip
      closeOrNested n

def header : Parser Unit := do
  trash $ pstring "/***"
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
  trash $ pstring "/**"
  parseLines acc
where
  docLineEnd : Parser Bool := do
    ( (fun _ => false) <$> newline ) <|> ( (fun _ => true) <$> pstring "*/" )
  parseLines (acc : Array String) : Parser Doc := do
    ws
    if ← ptest <| pstring "*/" then
      return acc
    if ← ptest <| pchar '*' then
      trash $ pchar? ' '
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
  trash $ pchar op
  wsCmt
  let res ← p
  wsCmt
  trash $ pchar cl
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
  trash $ pstring "EVALUE"
  wsCmt
  let (ident, offset) ←
    delimited do
      let ident ← pident
      wsCmt
      let offset ←
        if ← ptest $ pchar '=' then
          wsCmt
          let i ← pint
          pure (some i)
        else pure none
      wsCmt
      pure (ident, offset)
  wsCmt
  trash $ pchar? ','
  return ⟨doc?, ident, offset, ifdef?⟩

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
    loop i acc none
  else if ← isEof then
    return acc
  else
    let variant ← pvariant ifdef?
    let acc := acc.push variant
    loop i.succ acc ifdef?

partial def penum : Parser Enum := do
  wsCmt
  let doc ← pdoc
  wsCmt
  trash $ pstring "enum"
  wsCmt
  trash $ pstring "ENUM"
  wsCmt
  let ident ← delimited pident
  wsCmt
  if ← ptest $ pchar ':' then
    wsCmt
    trash $ pchar? 'u'
    trash $ pstring "int32_t"
    wsCmt
  let variants ← delimited (delim := .brace) pvariants
  wsCmt
  trash $ pchar? ';'
  return ⟨doc, ident, variants⟩

partial def penums (acc : Enums := #[]) : Parser Enums := do
  match ← skipUntil penum with
  | none => return acc
  | some enum => acc.push enum |> penums

def pfile : Parser Enums := do
  trash $ ptry header
  let enums ← penums
  wsCmt
  if ← isEof then
    return enums
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
  | .success _ι a => return a
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
  let meta ← p.metadata
  return meta.modified

/-- True if `lft` was modified more recently than `rgt`, or `rgt` does not exist. -/
def moreRecentThan (lft rgt : FilePath) : IO Bool := do
  if ¬ (← rgt.pathExists) then
    println! "  target does not exist"
    return true
  else
    let lTime ← lft.modified
    let rTime ← rgt.modified
    if rTime < lTime then
      println! "  source is more recent than target"
      return true
    else
      println! "  target is more recent than source"
      return false

end FilePath

def updateLeanFile (cpp lean : FilePath) : IO Unit := do
  println! "- {cpp} → {lean}"
  if ← cpp.moreRecentThan lean then
    println! "  updating"
    writeLean cpp lean
    println! "  done"

def updateLean (cppDir leanDir : FilePath) : IO Unit := do
  let pairs := [
    ("cvc5_kind.h", "Kind.lean"),
    ("cvc5_proof_rule.h", "ProofRule.lean"),
    ("cvc5_skolem_id.h", "SkolemId.lean"),
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



-- namespace cvc5.PreBuild.Test

-- open Parser

-- def mlCommentStr := r##"
-- /** some comment */
-- /**
-- some
-- comment
-- */
-- "##

-- #eval do
--   let _ ← parseContentWith
--     (do
--       wsCmt
--       trash $ pdoc
--       wsCmt
--       trash $ pdoc
--       wsCmt
--     )
--     mlCommentStr
--   println! "done"

-- def docStr := r##"
-- // comment
-- /**
--  * The kind of a cvc5 Sort.
--  *
--  * \internal
--  *
--  * Note that the API type `cvc5::SortKind` roughly corresponds to
--  * `cvc5::internal::Kind`, but is a different type. It hides internal kinds
--  * that should not be exported to the API, and maps all kinds that we want to
--  * export to its corresponding internal kinds. The underlying type of
--  * `cvc5::Kind` must be signed (to enable range checks for validity). The size
--  * of this type depends on the size of `cvc5::internal::Kind`
--  * (`NodeValue::NBITS_KIND`, currently 10 bits, see expr/node_value.h).
--  */
-- enum ENUM(Blah)
-- {
-- };
-- "##

-- #eval do
--   let _ ← parseContentWith
--     (do let _ ← penum ; wsCmt)
--     docStr
--   println! "done"

-- def sortKindStr := r##"
-- // clang-format off
-- /**
--  * The kind of a cvc5 Sort.
--  *
--  * \internal
--  *
--  * Note that the API type `cvc5::SortKind` roughly corresponds to
--  * `cvc5::internal::Kind`, but is a different type. It hides internal kinds
--  * that should not be exported to the API, and maps all kinds that we want to
--  * export to its corresponding internal kinds. The underlying type of
--  * `cvc5::Kind` must be signed (to enable range checks for validity). The size
--  * of this type depends on the size of `cvc5::internal::Kind`
--  * (`NodeValue::NBITS_KIND`, currently 10 bits, see expr/node_value.h).
--  */
-- enum ENUM(SortKind)
-- {
--   /**
--    * Internal kind.
--    *
--    * This kind serves as an abstraction for internal kinds that are not exposed
--    * via the API but may appear in terms returned by API functions, e.g.,
--    * when querying the simplified form of a term.
--    *
--    * \rst
--    * .. note:: Should never be created via the API.
--    * \endrst
--    */
--   EVALUE(INTERNAL_SORT_KIND = -2),
--   /**
--    * Undefined kind.
--    *
--    * \rst
--    * .. note:: Should never be exposed or created via the API.
--    * \endrst
--    */
--   EVALUE(UNDEFINED_SORT_KIND = -1),
--   /**
--    * Null kind.
--    *
--    * The kind of a null sort (Sort::Sort()).
--    *
--    * \rst
--    * .. note:: May not be explicitly created via API functions other than
--    *           :cpp:func:`Sort::Sort()`.
--    * \endrst
--    */
--   EVALUE(NULL_SORT),

--   /* Sort Kinds ------------------------------------------------------------ */
--   /**
--    * An abstract sort.
--    *
--    * An abstract sort represents a sort whose parameters or argument sorts are
--    * unspecified. For example, `mkAbstractSort(BITVECTOR_SORT)` returns a
--    * sort that represents the sort of bit-vectors whose bit-width is
--    * unspecified.
--    *
--    * - Create Sort of this Kind with:
--    *
--    *   - Solver::mkAbstractSort(SortKind) const
--    */
--   EVALUE(ABSTRACT_SORT),
--   /**
--    * An array sort, whose argument sorts are the index and element sorts of the
--    * array.
--    *
--    * - Create Sort of this Kind with:
--    *
--    *   - Solver::mkArraySort(Sort, Sort) const
--    */
--   EVALUE(ARRAY_SORT),
--   /**
--    * A bag sort, whose argument sort is the element sort of the bag.
--    *
--    * - Create Sort of this Kind with:
--    *
--    *   - Solver::mkBagSort(Sort) const
--    */
--   EVALUE(BAG_SORT),
--   /**
--    * The Boolean sort.
--    *
--    * - Create Sort of this Kind with:
--    *
--    *   - Solver::getBooleanSort() const
--    */
--   EVALUE(BOOLEAN_SORT),
--   /**
--    * A bit-vector sort, parameterized by an integer denoting its bit-width.
--    *
--    * - Create Sort of this Kind with:
--    *
--    *   - Solver::mkBitVectorSort(uint32_t) const
--    */
--   EVALUE(BITVECTOR_SORT),
--   /**
--    * A datatype sort.
--    *
--    * - Create Sort of this Kind with:
--    *
--    *   - Solver::mkDatatypeSort(DatatypeDecl)
--    *   - Solver::mkDatatypeSorts(const std::vector<DatatypeDecl>&)
--    */
--   EVALUE(DATATYPE_SORT),
--   /**
--    * A finite field sort, parameterized by a size.
--    *
--    * - Create Sort of this Kind with:
--    *
--    *   - Solver::mkFiniteFieldSort(const std::string&, uint32_t base) const
--    */
--   EVALUE(FINITE_FIELD_SORT),
--   /**
--    * A floating-point sort, parameterized by two integers denoting its
--    * exponent and significand bit-widths.
--    *
--    * - Create Sort of this Kind with:
--    *
--    *   - Solver::mkFloatingPointSort(uint32_t, uint32_t) const
--    */
--   EVALUE(FLOATINGPOINT_SORT),
--   /**
--    * A function sort with given domain sorts and codomain sort.
--    *
--    * - Create Sort of this Kind with:
--    *
--    *   - Solver::mkFunctionSort(const std::vector<Sort>&, Sort) const
--    */
--   EVALUE(FUNCTION_SORT),
--   /**
--    * The integer sort.
--    *
--    * - Create Sort of this Kind with:
--    *
--    *   - Solver::getIntegerSort() const
--    */
--   EVALUE(INTEGER_SORT),
--   /**
--    * The real sort.
--    *
--    * - Create Sort of this Kind with:
--    *
--    *   - Solver::getRealSort() const
--    */
--   EVALUE(REAL_SORT),
--   /**
--    * The regular language sort.
--    *
--    * - Create Sort of this Kind with:
--    *
--    *   - Solver::getRegExpSort() const
--    */
--   EVALUE(REGLAN_SORT),
--   /**
--    * The rounding mode sort.
--    *
--    * - Create Sort of this Kind with:
--    *
--    *   - Solver::getRoundingModeSort() const
--    */
--   EVALUE(ROUNDINGMODE_SORT),
--   /**
--    * A sequence sort, whose argument sort is the element sort of the sequence.
--    *
--    * - Create Sort of this Kind with:
--    *
--    *   - Solver::mkSequenceSort(Sort) const
--    */
--   EVALUE(SEQUENCE_SORT),
--   /**
--    * A set sort, whose argument sort is the element sort of the set.
--    *
--    * - Create Sort of this Kind with:
--    *
--    *   - Solver::mkSetSort(Sort) const
--    */
--   EVALUE(SET_SORT),
--   /**
--    * The string sort.
--    *
--    * - Create Sort of this Kind with:
--    *
--    *   - Solver::getStringSort() const
--    */
--   EVALUE(STRING_SORT),
--   /**
--    * A tuple sort, whose argument sorts denote the sorts of the direct children
--    * of the tuple.
--    *
--    * - Create Sort of this Kind with:
--    *
--    *   - Solver::mkTupleSort(const std::vector<Sort>&) const
--    */
--   EVALUE(TUPLE_SORT),
--   /**
--    * A nullable sort, whose argument sort denotes the sort of the direct child
--    * of the nullable.
--    *
--    * - Create Sort of this Kind with:
--    *
--    *   - Solver::mkNullableSort(const Sort&) const
--    */
--   EVALUE(NULLABLE_SORT),
--   /**
--    * An uninterpreted sort.
--    *
--    * - Create Sort of this Kind with:
--    *
--    *   - Solver::mkUninterpretedSort(const std::optional<std::string>&) const
--    */
--   EVALUE(UNINTERPRETED_SORT),
--   /* ----------------------------------------------------------------------- */
--   /** Marks the upper-bound of this enumeration. */
--   EVALUE(LAST_SORT_KIND)
-- };
-- "##

-- #eval do
--   let enums ← parseContent sortKindStr
--   println! "parsed {enums.size} enum(s)"
--   for enum in enums do
--     println! "- enum `{enum.ident}`, {enum.variants.size} variant(s)"

-- #eval do
--   let enums ← parseFile ".lake/cvc5-macOS-arm64-static/include/cvc5/cvc5_kind.h"
--   println! "parsed {enums.size} enum(s)"
--   for enum in enums do
--     println! "- enum `{enum.ident}`, {enum.variants.size} variant(s)"

-- #eval do
--   let enums ← parseFile ".lake/cvc5-macOS-arm64-static/include/cvc5/cvc5_proof_rule.h"
--   println! "parsed {enums.size} enum(s)"
--   for enum in enums do
--     println! "- enum `{enum.ident}`, {enum.variants.size} variant(s)"

-- #eval do
--   let enums ← parseFile ".lake/cvc5-macOS-arm64-static/include/cvc5/cvc5_skolem_id.h"
--   println! "parsed {enums.size} enum(s)"
--   for enum in enums do
--     println! "- enum `{enum.ident}`, {enum.variants.size} variant(s)"

--   enums.writeToFile "test.lean"

-- end Test
