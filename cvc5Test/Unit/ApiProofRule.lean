import cvc5Test.Init

/-! # Black box testing of the `Op` type

- <https://github.com/cvc5/cvc5/blob/main/test/unit/api/cpp/api_proof_rule_black.cpp>
-/

namespace cvc5.Test

test![TestApiBlackProofRule, proofRuleToString] _tm => do
  for pr in ProofRule.listAll do
    -- if this assertion fails, the switch is missing rule `pr`.
    assertNe pr.toString "?"

test![TestApiBlackProofRule, proofRuleHash] _tm => do
  for pr in ProofRule.listAll do
    assertEq pr.hash pr.toCtorIdx

test![TestApiBlackProofRewriteRule, proofRuleToString] _tm => do
  for pr in ProofRewriteRule.listAll do
    -- if this assertion fails, the switch is missing rule `pr`.
    assertNe pr.toString "?"

test![TestApiBlackProofRewriteRule, proofRuleHash] _tm => do
  for pr in ProofRewriteRule.listAll do
    assertEq pr.hash pr.toCtorIdx
