import cvc5



namespace Test

/-- info: bool = `Bool` -/
#guard_msgs in #eval Cvc5.runIO do
  let bool ← Cvc5.getBooleanSort
  println! "bool = `{bool}`"

/-- error: not a function sort: Bool -/
#guard_msgs in #eval Cvc5.runIO do
  let bool ← Cvc5.getBooleanSort
  let _sorts ← bool.getFunctionDomainSorts

/-- info: Bool.substitute [Bool → Int] = Int -/
#guard_msgs in #eval Cvc5.runIO do
  let bool ← Cvc5.getBooleanSort
  let int ← Cvc5.getIntegerSort
  let sub ← bool.substitute #[bool] #[int]
  println! "{bool}.substitute [{bool} → {int}] = {sub}"

/-- info: version = `1.2.1` -/
#guard_msgs in #eval Cvc5.runIO do
  let solver ← Cvc5.Solver.new
  let version ← solver.getVersion
  println! "version = `{version}`"

/--
info: b1 = `b1`
b2 = `b2`
b1_and_b2 = `(and b1 b2)`
b3 = `b3`
b4 = `b4`
conj = `(and b1 b2 b3 b4)`
-/
#guard_msgs in #eval Cvc5.runIO do
  let bool ← Cvc5.getBooleanSort
  let solver ← Cvc5.Solver.new
  let b1 ← solver.declareFun "b1" #[] bool
  println! "b1 = `{b1}`"
  let b2 ← solver.declareFun "b2" #[] bool
  println! "b2 = `{b2}`"
  let b1_and_b2 ← Cvc5.Term.mk .AND #[b1, b2]
  println! "b1_and_b2 = `{b1_and_b2}`"
  let b3 ← solver.declareFun "b3" #[] bool
  println! "b3 = `{b3}`"
  let b4 ← solver.declareFun "b4" #[] bool
  println! "b4 = `{b4}`"
  -- let conj ← b1.mkInto .AND #[b2, b3, b4]
  let conj ← Cvc5.Term.mk .AND #[b1, b2, b3, b4]
  println! "conj = `{conj}`"

/-- error: expecting a Boolean subexpression -/
#guard_msgs in #eval Cvc5.runIO do
  let bool ← Cvc5.getBooleanSort
  let int ← Cvc5.getIntegerSort
  let solver ← Cvc5.Solver.new
  let b1 ← solver.declareFun "b1" #[] int
  let i1 ← solver.declareFun "i1" #[] int
  let shouldFail ← b1.and i1
  throw <| Cvc5.Error.error s!"should have failed: `{shouldFail}`"
  return ()
