import cvc5Test.Init

/-! # Black box testing of the `Op` type

- <https://github.com/cvc5/cvc5/blob/main/test/unit/api/cpp/api_proof_rule_black.cpp>
-/

namespace cvc5.Test

test![TestApiBlackProofRule, proofRuleToString] do
  for idx in [ProofRule.ASSUME.toCtorIdx : ProofRule.UNKNOWN.toCtorIdx] do
    let pr := ProofRule.ofNat idx
    -- if this assertion fails, the switch is missing rule `pr`.
    assertNe pr.toString "?"

test![TestApiBlackProofRule, proofRuleHash] do
  for idx in [ProofRule.ASSUME.toCtorIdx : ProofRule.UNKNOWN.toCtorIdx] do
    let pr := ProofRule.ofNat idx
    assertEq pr.hash ⟨pr.toCtorIdx⟩

test![TestApiBlackProofRewriteRule, proofRuleToString] do
  for idx in [ProofRule.ASSUME.toCtorIdx : ProofRule.UNKNOWN.toCtorIdx] do
    let pr := ProofRule.ofNat idx
    -- if this assertion fails, the switch is missing rule `pr`.
    assertNe pr.toString "?"

test![TestApiBlackProofRewriteRule, proofRuleHash] do
  for idx in [ProofRule.ASSUME.toCtorIdx : ProofRule.UNKNOWN.toCtorIdx] do
    let pr := ProofRule.ofNat idx
    assertEq pr.hash ⟨pr.toCtorIdx⟩
