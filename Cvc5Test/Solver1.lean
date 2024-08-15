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

/-- info:
confirmed sat result
[getValue] n1 = 0, n2 = 0, b = true
[getValues] n1 = 0, n2 = 0, b = true
-/
test! tm => do
  Solver.setOption "produce-models" "true"
  Solver.setLogic "QF_LIA"

  let bool := tm.getBooleanSort
  let int := tm.getIntegerSort

  let n1 ← Solver.declareFun "n1" #[] int true
  let n2 ← Solver.declareFun "n2" #[] int true

  let b ← Solver.declareFun "b" #[] bool true

  let n1_eq_n2 ← tm.mkTerm Kind.EQUAL #[n1, n2]
  let n1_ne_n2 ← tm.mkTerm Kind.NOT #[n1_eq_n2]
  let ite ← tm.mkTerm Kind.ITE #[b, n1_eq_n2, n1_ne_n2]

  Solver.assertFormula ite
  Solver.assertFormula n1_eq_n2

  let isSat? ← Solver.checkSat?
  assertEq isSat? true
  println! "confirmed sat result"

  let n1Val ← Solver.getValue n1
  let n2Val ← Solver.getValue n2
  let bVal ← Solver.getValue b

  println! "[getValue] n1 = {n1Val}, n2 = {n2Val}, b = {bVal}"

  let terms := #[n1, n2, b]
  let values ← Solver.getValues terms

  println! "[getValues] n1 = {values.get! 0}, n2 = {values.get! 1}, b = {values.get! 2}"

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
