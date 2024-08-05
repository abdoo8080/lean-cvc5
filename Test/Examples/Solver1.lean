import Test.Init

namespace cvc5.Test

def work : IO Unit := Smt.run! do
  Smt.setOption "produce-proofs" "true"

  Smt.setLogic' Logic.qf_lia

  let n1 ← Smt.declareConst "n1" Int
  let n2 ← Smt.declareConst "n2" Int

  let b ← Smt.declareConst "b" Bool

  let eq ← Smt.mkEqual n1 n2
  let neq ← Smt.mkNot eq
  let ite ← Smt.mkIte b eq neq

  Smt.assertFormula ite
  Smt.assertFormula eq

  match ← Smt.checkSat? with
  | none =>
    panic! "got a timeout"
  | some false =>
    panic! "unexpected `unsat` result"
  | some true =>
    println! "confirmed `sat` result"

  Smt.resetAssertions

  let imp1 ← Smt.mkImplies b eq
  let not_b ← Smt.mkNot b
  let imp2 ← Smt.mkImplies not_b neq

  Smt.assertFormula imp1
  Smt.assertFormula imp2
  Smt.assertFormula eq
  Smt.assertFormula not_b

  match ← Smt.checkSat? with
  | none => panic! "got a timeout"
  | some false => println! "confirmed `unsat` result"
  | some true => panic! "unexpected `sat` result"

  let proofs ← Smt.getProof

  println! "proof:"
  for p in proofs do
    println! "- {p.getResult}"

#eval work
