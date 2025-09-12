import cvc5Test.Init



namespace cvc5.Test



namespace Srt

def testSort (getSort : Env cvc5.Sort) : IO Unit := do
  let res ← Env.run do
    let sort ← getSort
    println! "sort := `{sort}`"
  match res with
  | .ok () => return ()
  | .error e => IO.eprintln s!"ERROR\n{e}"

/-- info: sort := `Bool` -/
#guard_msgs in #eval testSort getBooleanSort
/-- info: sort := `Int` -/
#guard_msgs in #eval testSort getIntegerSort
/-- info: sort := `Real` -/
#guard_msgs in #eval testSort getRealSort
/-- info: sort := `RegLan` -/
#guard_msgs in #eval testSort getRegExpSort
/-- info: sort := `String` -/
#guard_msgs in #eval testSort getStringSort
/-- info: sort := `RoundingMode` -/
#guard_msgs in #eval testSort getRoundingModeSort

/-- info: sort := `(Array Int String)` -/
#guard_msgs in #eval testSort do
  let int ← getIntegerSort
  let string ← getStringSort
  mkArraySort int string

/-- info: sort := `(_ BitVec 5)` -/
#guard_msgs in #eval testSort do
  mkBitVectorSort 5

/-- info: sort := `(_ FloatingPoint 10 10)` -/
#guard_msgs in #eval testSort do
  mkFloatingPointSort 10 10

/-- info: sort := `(_ FiniteField 5)` -/
#guard_msgs in #eval testSort do
  mkFiniteFieldSort 5 10

/-- info: sort := `(-> Int Real String String)` -/
#guard_msgs in #eval testSort do
  let int ← getIntegerSort
  let real ← getRealSort
  let string ← getStringSort
  mkFunctionSort #[int, real, string] string

/-- info: sort := `(-> Int Real String Bool)` -/
#guard_msgs in #eval testSort do
  let int ← getIntegerSort
  let real ← getRealSort
  let string ← getStringSort
  mkPredicateSort #[int, real, string]

/-- info: sort := `(Tuple Int Real String)` -/
#guard_msgs in #eval testSort do
  let int ← getIntegerSort
  let real ← getRealSort
  let string ← getStringSort
  mkTupleSort #[int, real, string]

/-- info: sort := `(Set String)` -/
#guard_msgs in #eval testSort do
  let string ← getStringSort
  mkSetSort string

/-- info: sort := `(Array ? ?)` -/
#guard_msgs in #eval testSort do
  mkAbstractSort SortKind.ARRAY_SORT

/-- info: sort := `u` -/
#guard_msgs in #eval testSort do
  mkUninterpretedSort "u"

/-- info: sort := `(Nullable String)` -/
#guard_msgs in #eval testSort do
  let string ← getStringSort
  mkNullableSort string

/-- info: sort := `p` -/
#guard_msgs in #eval testSort do
  mkParamSort "p"

end Srt



namespace Term

def testTerm (getTerm : Env Term) : IO Unit := do
  let res ← Env.run do
    let term ← getTerm
    println! "term := `{term}`"
  match res with
  | .ok () => return ()
  | .error e => IO.eprintln s!"ERROR\n{e}"

/-- info: term := `false` -/
#guard_msgs in #eval testTerm do
  mkBoolean false

/-- info: term := `5` -/
#guard_msgs in #eval testTerm do
  mkInteger 5

/-- info: term := `(/ 5 2)` -/
#guard_msgs in #eval testTerm do
  mkReal 5 2

/-- info: term := `(+ 5 3 7)` -/
#guard_msgs in #eval testTerm do
  let t1 ← mkInteger 5
  let t2 ← mkInteger 3
  let t3 ← mkInteger 7
  mkTerm .ADD #[t1, t2, t3]

/-- info: term := `myConst` -/
#guard_msgs in #eval testTerm do
  let bool ← getBooleanSort
  mkConst bool "myConst"

/-- info: term := `myVar` -/
#guard_msgs in #eval testTerm do
  let bool ← getBooleanSort
  mkVar bool "myVar"

end Term
