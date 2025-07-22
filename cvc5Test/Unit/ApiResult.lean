import cvc5Test.Init

/-! # Black box testing of the `Op` type

- <https://github.com/cvc5/cvc5/blob/main/test/unit/api/cpp/api_op_black.cpp>
-/

namespace cvc5.Test

test![TestApiBlackResult, isNull] do
  -- lean API does not expose null results
  assertTrue true

test![TestApiBlackResult, equalHash] do
  let u ← cvc5.mkUninterpretedSort "u"
  let solver ← Solver.new
  let x ← solver.declareFun "x" #[] u
  let x_eq_x ← x.eq x
  solver.assertFormula x_eq_x
  -- skipping null-result-related checks
  let res1 ← solver.checkSat
  let res2 ← solver.checkSat
  solver.assertFormula (← x_eq_x.not)
  let res3 ← solver.checkSat
  assertEq res1 res2
  assertNe res1 res3
  assertNe res2 res3
  assertEq res1.toString "sat"
  assertEq res2.toString "sat"
  assertEq res3.toString "unsat"
  assertEq res1.hash res2.hash
  assertNe res1.hash res3.hash
  assertNe res2.hash res3.hash

test![TestApiBlackResult, isSat] do
  let u ← cvc5.mkUninterpretedSort "u"
  let solver ← Solver.new
  let x ← solver.declareFun "x" #[] u
  solver.assertFormula (← x.eq x)
  let res ← solver.checkSat
  assertTrue res.isSat
  assertFalse res.isUnsat
  assertFalse res.isUnknown
  -- not part of the original test
  let ue := res.getUnknownExplanation
  assertEq ue .UNKNOWN_REASON
  assertEq ue.toString "UNKNOWN_REASON"
  assertEq res.getUnknownExplanation? none

test![TestApiBlackResult, isUnsat] do
  let u ← cvc5.mkUninterpretedSort "u"
  let solver ← Solver.new
  let x ← solver.declareFun "x" #[] u
  solver.assertFormula (← (← x.eq x).not)
  let res ← solver.checkSat
  assertFalse res.isSat
  assertTrue res.isUnsat
  assertFalse res.isUnknown
  -- not part of the original test
  let ue := res.getUnknownExplanation
  assertEq ue .UNKNOWN_REASON
  assertEq ue.toString "UNKNOWN_REASON"
  assertEq res.getUnknownExplanation? none

test![TestApiBlackResult, isUnknown] do
  let solver ← Solver.new
  solver.setLogic "QF_NIA"
  solver.setOption "incremental" "false"
  solver.setOption "solve-real-as-int" "true"
  let realSort ← cvc5.getRealSort
  let x ← solver.declareFun "x" #[] realSort
  let zero ← Term.mkReal 0
  let one ← Term.mkReal 1
  solver.assertFormula (← Term.mk .LT #[zero, x])
  solver.assertFormula (← Term.mk .LT #[x, one])
  let res ← solver.checkSat
  assertFalse res.isSat
  assertFalse res.isUnsat
  assertTrue res.isUnknown
  let ue := res.getUnknownExplanation
  assertEq ue .INCOMPLETE
  assertEq ue.toString "INCOMPLETE"
  let ue? := res.getUnknownExplanation?
  assertTrue ue?.isSome
  if let some ue := ue? then
    assertEq ue .INCOMPLETE
    assertEq ue.toString "INCOMPLETE"
