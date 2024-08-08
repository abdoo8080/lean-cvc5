import Cvc5Test.Init

namespace cvc5.Test

/-- info:
bvSort = (_ BitVec 1)
-/
#guard_msgs in
#eval IO.run do
  let tm ← TermManager.new

  let bvSort ←
    tm.mkBitVectorSort 0
    |> assertOk
  println! "bvSort = {bvSort}"



/-- info: -/
#guard_msgs in #eval Solver.run! do
  Solver.setOption "produce-models" "true"
  |> assertSolverOk
  Solver.setOption "produce-proofs" "true"
  |> assertSolverOk

  Solver.setOption "does-not-exist" "not-even-a-value"
  |> assertSolverCvc5Error "unrecognized option: does-not-exist."

  Solver.getProof
  |> assertSolverCvc5Error "cannot get proof unless in unsat mode."

  let isSat? ← Solver.checkSat?
  assertEq isSat? true "checkSat should be sat"

  Solver.getProof
  |> assertSolverCvc5Error "cannot get proof unless in unsat mode."
