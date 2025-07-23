import cvc5Test.Init

namespace cvc5.Test

def solver1Parse : IO Unit := cvc5.runIO do
  let solver1 ← Solver.new
  solver1.parseSmtLib "
(set-logic QF_LIA)

(declare-fun n1 () Int)
(declare-fun n2 () Int)

(declare-fun b () Bool)

(assert (ite b (= n1 n2) (not (= n1 n2))))
(assert (= n1 n2))
  "
  match ← solver1.checkSat? with
  | none =>
    panic! "got a timeout"
  | some false =>
    panic! "unexpected `unsat` result"
  | some true =>
    println! "confirmed `sat` result"



  let solver2 ← Solver.new
  solver2.parseSmtLib "
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

  match ← solver2.checkSat? with
  | some false => println! "confirmed `unsat` result"
  | none => panic! "got a timeout"
  | some true => panic! "unexpected `sat` result"

  let proofs ← solver2.getProof

  println! "proof:"
  for p in proofs do
    println! "- {p.getResult}"

/-- info:
confirmed `sat` result
confirmed `unsat` result
proof:
- (let ((_let_1 (not b))) (let ((_let_2 (= n1 n2))) (not (and (=> b _let_2) (=> _let_1 (not _let_2)) _let_2 _let_1))))
-/
#guard_msgs in
  #eval solver1Parse
