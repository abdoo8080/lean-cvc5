import Cvc5Test.Init

namespace cvc5.Test

/-- info: -/
#guard_msgs in #eval Solver.run! do
  Solver.setOption "produce-models" "true"
  |> assertOk
  Solver.setOption "produce-proofs" "true"
  |> assertOk

  Solver.setOption "does-not-exist" "not-even-a-value"
  |> assertError "unrecognized option: does-not-exist."

  Solver.getProof
  |> assertError "cannot get proof unless in unsat mode."

  let isSat? ← Solver.checkSat?
  assertEq isSat? true "checkSat should be sat"

  Solver.getProof
  |> assertError "cannot get proof unless in unsat mode."
