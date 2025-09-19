import cvc5Test.Init

/-! # Black box testing of the `Op` type

- <https://github.com/cvc5/cvc5/blob/main/test/unit/api/cpp/api_op_black.cpp>
-/

namespace cvc5.Test

open Env

test![TestApiBlackResult, isNull] do
  -- lean API does not expose null results
  assertTrue true

test![TestApiBlackResult, equalHash] solver => do
  let u ← mkUninterpretedSort "u"
  let x ← solver.declareFun "x" #[] u
  let x_eq_x ← mkTerm .EQUAL #[x, x]
  solver.assertFormula x_eq_x
  -- skipping null-result-related checks
  let res1 ← solver.checkSat
  let res2 ← solver.checkSat
  solver.assertFormula (← mkTerm .NOT #[x_eq_x])
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

test![TestApiBlackResult, isSat] solver => do
  let u ← mkUninterpretedSort "u"
  let x ← solver.declareFun "x" #[] u
  solver.assertFormula (← mkTerm .EQUAL #[x, x])
  let res ← solver.checkSat
  assertTrue res.isSat
  assertFalse res.isUnsat
  assertFalse res.isUnknown
  -- not part of the original test
  let ue := res.getUnknownExplanation
  assertEq ue .UNKNOWN_REASON
  assertEq ue.toString "UNKNOWN_REASON"
  assertEq res.getUnknownExplanation? none

test![TestApiBlackResult, isUnsat] solver => do
  let u ← mkUninterpretedSort "u"
  let x ← solver.declareFun "x" #[] u
  solver.assertFormula (← mkTerm .NOT #[← mkTerm .EQUAL #[x, x]])
  let res ← solver.checkSat
  assertFalse res.isSat
  assertTrue res.isUnsat
  assertFalse res.isUnknown
  -- not part of the original test
  let ue := res.getUnknownExplanation
  assertEq ue .UNKNOWN_REASON
  assertEq ue.toString "UNKNOWN_REASON"
  assertEq res.getUnknownExplanation? none

test![TestApiBlackResult, isUnknown] solver => do
  solver.setLogic "QF_NIA"
  solver.setOption "incremental" "false"
  solver.setOption "solve-real-as-int" "true"
  let realSort ← getRealSort
  let x ← solver.declareFun "x" #[] realSort
  let zero := ← mkReal 0
  let one := ← mkReal 1
  solver.assertFormula (← mkTerm .LT #[zero, x])
  solver.assertFormula (← mkTerm .LT #[x, one])
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
