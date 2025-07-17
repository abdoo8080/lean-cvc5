import cvc5



namespace Cvc5.Test

/-- info: bool = `Bool` -/
#guard_msgs in #eval Env.runIO do
  let bool ← Env.getBooleanSort
  println! "bool = `{bool}`"

/-- error: [error] not a function sort: Bool -/
#guard_msgs in #eval Env.runIO do
  let bool ← Env.getBooleanSort
  let _sorts ← bool.getFunctionDomainSorts

/-- info: x = `x` -/
#guard_msgs in #eval Env.runIO do
  let bool ← Env.getBooleanSort
  let solver ← Solver.new
  let x ← solver.declareFun "x" #[] bool
  println! "x = `{x}`"
