import cvc5Test.Init

/-! # Black box testing of the `Op` type

- <https://github.com/cvc5/cvc5/blob/main/test/unit/api/cpp/api_proof_rule_black.cpp>
-/

namespace cvc5.Test

test![TestApiBlackProofRule, proofRuleToString] _tm => do
  for idx in [ProofRule.ASSUME.ctorIdx : ProofRule.UNKNOWN.ctorIdx] do
    let pr := ProofRule.ofNat idx
    -- if this assertion fails, the switch is missing rule `pr`.
    assertNe pr.toString "?"

test![TestApiBlackProofRule, proofRuleHash] _tm => do
  for idx in [ProofRule.ASSUME.ctorIdx : ProofRule.UNKNOWN.ctorIdx] do
    let pr := ProofRule.ofNat idx
    assertEq pr.hash ⟨pr.ctorIdx⟩

test![TestApiBlackProofRewriteRule, proofRuleToString] _tm => do
  for idx in [ProofRule.ASSUME.ctorIdx : ProofRule.UNKNOWN.ctorIdx] do
    let pr := ProofRule.ofNat idx
    -- if this assertion fails, the switch is missing rule `pr`.
    assertNe pr.toString "?"

test![TestApiBlackProofRewriteRule, proofRuleHash] _tm => do
  for idx in [ProofRule.ASSUME.ctorIdx : ProofRule.UNKNOWN.ctorIdx] do
    let pr := ProofRule.ofNat idx
    assertEq pr.hash ⟨pr.ctorIdx⟩
