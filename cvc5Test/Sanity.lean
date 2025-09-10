import cvc5Test.Init



namespace cvc5.Test

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
/-- info: sort := `RoundingMode` -/
#guard_msgs in #eval testSort getRoundingModeSort
/-- info: sort := `String` -/
#guard_msgs in #eval testSort getStringSort

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
  mkFiniteFieldSortFromString "5" 10

/-- info: sort := `(-> Int Real String String)` -/
#guard_msgs in #eval testSort do
  let int ← getIntegerSort
  let real ← getRealSort
  let string ← getStringSort
  cvc5.mkFunctionSort #[int, real, string] string

/-- info: sort := `(-> Int Real String Bool)` -/
#guard_msgs in #eval testSort do
  let int ← getIntegerSort
  let real ← getRealSort
  let string ← getStringSort
  cvc5.mkPredicateSort #[int, real, string]
