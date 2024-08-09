import Cvc5Test.Init

namespace cvc5.Test

/--
error: simp made no progress
---
info:
-/
test! tm => do
  let mkBvSort (n : UInt32) :=
    tm.mkBitVectorSort n -- cannot prove `0 < n`
  let _ := mkBvSort 0
  let _ := mkBvSort 1

test! _tm =>  do
  Solver.setOption "produce-models" "true"
  |> assertOk
  Solver.setOption "produce-proofs" "true"
  |> assertOk

  -- bad option
  Solver.setOption "does-not-exist" "true"
  |> assertCvc5Error "unrecognized option: does-not-exist."
  -- bad value
  Solver.setOption "produce-models" "7"
  |> assertCvc5Error "
Error in option parsing: Argument '7' for bool option produce-models is not a bool constant
  ".trim

  Solver.getProof
  |> assertCvc5Error "cannot get proof unless in unsat mode."

  let isSat? ← Solver.checkSat?
  assertEq isSat? true "checkSat should be sat"

  -- illegal `setOption`
  Solver.setOption "produce-proofs" "true"
  |> assertCvc5Error "
invalid call to 'setOption' for option 'produce-proofs', solver is already fully initialized
  ".trim

  -- `getProof` illegal in sat mode
  Solver.getProof
  |> assertCvc5Error "cannot get proof unless in unsat mode."
