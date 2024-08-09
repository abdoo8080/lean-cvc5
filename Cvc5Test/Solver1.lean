import Cvc5Test.Init

namespace cvc5.Test

/-- info:
confirmed sat result
-/
test! do
  Solver.parse "
(set-logic QF_LIA)

(declare-fun n1 () Int)
(declare-fun n2 () Int)

(declare-fun b () Bool)

(assert (ite b (= n1 n2) (not (= n1 n2))))
(assert (= n1 n2))
  "

  let isSat? ← Solver.checkSat?
  assertEq isSat? true
  println! "confirmed sat result"

test! tm => do
  Solver.setLogic "QF_LIA"

/-- info:
confirmed unsat result
proof:
- (let ((_let_1 (not b))) (let ((_let_2 (= n1 n2))) (not (and (=> b _let_2) (=> _let_1 (not _let_2)) _let_2 _let_1))))
-/
test! do
  Solver.parse "
(set-option :produce-proofs true)

(set-logic QF_LIA)

(declare-fun n1 () Int)
(declare-fun n2 () Int)

(declare-fun b () Bool)

(assert (=> b (= n1 n2)))
(assert (=> (not b) (not (= n1 n2))))
(assert (= n1 n2))
(assert (not b))
  "

  let isSat? ← Solver.checkSat?
  assertEq isSat? false
  println! "confirmed unsat result"

  let proofs ← Solver.getProof

  println! "proof:"
  for p in proofs do
    println! "- {p.getResult}"
