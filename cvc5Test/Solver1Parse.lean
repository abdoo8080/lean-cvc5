import cvc5Test.Init

namespace cvc5.Solver

/-- Parse a string containing SMT-LIB commands.

Commands that produce a result such as `(check-sat)`, `(get-model)`, ... are executed but the
results are ignored.
-/
def parseCommands (solver : cvc5.Solver) (query : String) : cvc5.Env (Array cvc5.Sort × Array cvc5.Term) := do
  let parser ← cvc5.InputParser.new solver
  let sm ← parser.getSymbolManager
  parser.setStringInput query .SMT_LIB_2_6
  while true do
    let cmd ← parser.nextCommand
    if cmd.isNull then break
    _ ← cmd.invoke solver sm
  let svs ← sm.getDeclaredSorts
  let tvs ← sm.getDeclaredTerms
  return (svs, tvs)

end Solver

namespace cvc5.Test

def solver1Parse : IO Unit := Env.runIO do
  let tm ← TermManager.new
  let query : Env (Option Bool) := do
    let solver ← Solver.new tm
    _ ← solver.parseCommands "
(set-logic QF_LIA)

(declare-fun n1 () Int)
(declare-fun n2 () Int)

(declare-fun b () Bool)

(assert (ite b (= n1 n2) (not (= n1 n2))))
(assert (= n1 n2))
    "
    solver.checkSat?

  match ← query with
  | none =>
    panic! "got a timeout"
  | some false =>
    panic! "unexpected `unsat` result"
  | some true =>
    println! "confirmed `sat` result"



  let query : Env (Array Proof) := do
    let solver ← Solver.new tm
    _ ← solver.parseCommands "
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

    match ← solver.checkSat? with
    | some false => println! "confirmed `unsat` result"
    | none => panic! "got a timeout"
    | some true => panic! "unexpected `sat` result"

    solver.getProof

  let proofs ← query

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
