import Test.Init

namespace cvc5.Test

-- #TODO same but without parsing, needs a few more lean-level cvc5 functions

def mkTerms : IO Unit := do
  let tm ← TermManager.new

  let query :=
    "
(set-logic QF_LIA)

(declare-fun n1 () Int)
(declare-fun n2 () Int)

(declare-fun b () Bool)

(assert (ite b (= n1 n2) (not (= n1 n2))))
(assert (= n1 n2))
    ".smtParseAnd Solver.checkSat?

  match ← Solver.run! tm query with
  | none =>
    panic! "got a timeout"
  | some false =>
    panic! "unexpected `unsat` result"
  | some true =>
    println! "confirmed `sat` result"



  let query : SolverM (Array Proof) :=
    "
(set-option :produce-proofs true)

(set-logic QF_LIA)

(declare-fun n1 () Int)
(declare-fun n2 () Int)

(declare-fun b () Bool)

(assert (=> b (= n1 n2)))
(assert (=> (not b) (not (= n1 n2))))
(assert (= n1 n2))
(assert (not b))
    ".smtParseAnd
    do
      match ← Solver.checkSat? with
      | none => panic! "got a timeout"
      | some false => println! "confirmed `unsat` result"
      | some true => panic! "unexpected `sat` result"

      Solver.getProof

  let proofs ← Solver.run! tm query

  println! "proof:"
  for p in proofs do
    println! "- {p.getResult}"

#eval mkTerms
