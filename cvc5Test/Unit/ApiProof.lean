/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Adrien Champion
-/
import cvc5Test.Init

/-! # Black box testing of the guards of the Lean API functions

- <https://github.com/cvc5/cvc5/blob/main/test/unit/api/cpp/api_proof_black.cpp>
-/

namespace cvc5.Test

section open Solver Env

def createProof (tm : TermManager) : Env Proof := do
  let solver ← Solver.new tm
  solver.setOption "produce-proofs" "true"
  let uSort ← tm.mkUninterpretedSort "u"
  let intSort ← tm.getIntegerSort
  let boolSort ← tm.getBooleanSort
  let uToIntSort ← tm.mkFunctionSort #[uSort] intSort
  let intPredSort ← tm.mkFunctionSort #[intSort] boolSort

  let x ← solver.declareFun "x" #[] uSort
  let y ← solver.declareFun "y" #[] uSort
  let f ← solver.declareFun "f" #[uSort] intSort
  let p ← solver.declareFun "p" #[intSort] boolSort
  let zero ← tm.mkInteger 0
  let one ← tm.mkInteger 1
  let f_x ← tm.mkTerm Kind.APPLY_UF #[f, x]
  let f_y ← tm.mkTerm Kind.APPLY_UF #[f, y]
  let sum ← tm.mkTerm Kind.ADD #[f_x, f_y]
  let p_0 ← tm.mkTerm Kind.APPLY_UF #[p, zero]
  let p_f_y ← tm.mkTerm Kind.APPLY_UF #[p, f_y]
  tm.mkTerm Kind.GT #[zero, f_x] >>= solver.assertFormula
  tm.mkTerm Kind.GT #[zero, f_y] >>= solver.assertFormula
  tm.mkTerm Kind.GT #[sum, one] >>= solver.assertFormula
  solver.assertFormula p_0
  tm.mkTerm .NOT #[p_f_y] >>= solver.assertFormula
  let res ← solver.checkSat
  if ¬ res.isUnsat then
    fail "expected unsat result in proof creation"

  let proof ← solver.getProof
  if h : 0 < proof.size then
    return proof[0]
  else
    fail "expected non-empty proof"

def createRewriteProof (tm : TermManager) : Env Proof := do
  let solver ← Solver.new tm
  solver.setOption "produce-proofs" "true"
  solver.setOption "proof-granularity" "dsl-rewrite"
  let intSort ← tm.getIntegerSort
  let x ← solver.declareFun "x" #[] intSort
  let zero ← tm.mkInteger 0
  let geq ← tm.mkTerm Kind.GEQ #[x, zero]
  let leq ← tm.mkTerm Kind.LEQ #[zero, x]
  tm.mkTerm Kind.DISTINCT #[geq, leq] >>= solver.assertFormula
  let res ← solver.checkSat
  if ¬ res.isUnsat then
    fail "expected unsat result in rewrite proof creation"

  let proof ← solver.getProof
  if h : 0 < proof.size then
    return proof[0]
  else
    fail "expected non-empty rewrite proof"

end

test![TestApiBlackProof, solver] do
  let proof := Proof.null ()
  assertEq proof.getRule ProofRule.UNKNOWN
  -- skipping test in original file for the hash being equal to the constructor index
  assertTrue proof.getResult.isNull
  assertTrue proof.getChildren.isEmpty
  assertTrue proof.getArguments.isEmpty

test![TestApiBlackProof, getRule] tm => do
  let proof ← createProof tm
  assertEq proof.getRule ProofRule.SCOPE

test![TestApiBlackProof, getRewriteRule] tm => do
  let mut proof ← createRewriteProof tm
  assertError
    "expected `getRule()` to return `DSL_REWRITE` or `THEORY_REWRITE`, got SCOPE instead."
    proof.getRewriteRule

  let mut rule : Option ProofRule := none
  let mut stack : Array Proof := #[proof]

  for _ in [0:1000] do
    if let some ProofRule.DSL_REWRITE := rule then
      break
    if h : 0 < stack.size then
      proof := stack[stack.size - 1]
      rule := proof.getRule
      stack := stack.pop ++ proof.getChildren
    else fail "expected `DSL_REWRITE` proof rule or non-empty stack"

  assertOkDiscard proof.getRewriteRule

test![TestApiBlackProof, getResult] solver => do
  let proof ← createProof solver
  let _ := proof.getResult

test![TestApiBlackProof, getChildren] solver => do
  let proof ← createProof solver
  let children := proof.getChildren
  assertFalse children.isEmpty

test![TestApiBlackProof, getArguments] solver => do
  let proof ← createProof solver
  let _ := proof.getArguments

test![TestApiBlackProof, equalhash] solver => do
  let x ← createProof solver
  let kids := x.getChildren
  if h : 0 < kids.size then
    let y := kids[0]
    let z := Proof.null ()

    assertTrue (x == x)
    assertFalse (x != x)
    assertFalse (x == y)
    assertTrue (x != y)
    assertFalse (x == z)
    assertTrue (x != z)

    assertTrue (x.hash == x.hash)
    assertFalse (x.hash == y.hash)
  else
    IO.eprintln "expected at least one kid"
