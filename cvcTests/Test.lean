import cvc5



namespace Test

/-- info: bool = `Bool` -/
#guard_msgs in #eval Cvc5.runIO do
  let bool ← Cvc5.getBooleanSort
  println! "bool = `{bool}`"

/-- error: [error] not a function sort: Bool -/
#guard_msgs in #eval Cvc5.runIO do
  let bool ← Cvc5.getBooleanSort
  let _sorts ← bool.getFunctionDomainSorts

/-- info: Bool.substitute [Bool → Int] = Int -/
#guard_msgs in #eval Cvc5.runIO do
  let bool ← Cvc5.getBooleanSort
  let int ← Cvc5.getIntegerSort
  let sub ← bool.substitute #[bool] #[int]
  println! "{bool}.substitute [{bool} → {int}] = {sub}"

/-- info: x = `x` -/
#guard_msgs in #eval Cvc5.runIO do
  let bool ← Cvc5.getBooleanSort
  let solver ← Cvc5.Solver.new
  let x ← solver.declareFun "x" #[] bool
  println! "x = `{x}`"
