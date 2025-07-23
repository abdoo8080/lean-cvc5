import cvc5



namespace Test

open cvc5 (Solver Srt Term)

/-- info: bool sort = `Bool` -/
#guard_msgs in #eval cvc5.runIO do
  let bool ← Srt.Boolean
  println! "bool sort = `{bool}`"

/-- error: not a function sort: Bool -/
#guard_msgs in #eval cvc5.runIO do
  let bool ← Srt.Boolean
  let _sorts ← bool.getFunctionDomainSorts

/-- info: Bool.substitute [Bool → Int] = Int -/
#guard_msgs in #eval cvc5.runIO do
  let bool ← Srt.Boolean
  let int ← Srt.Integer
  let sub ← bool.substitute #[bool] #[int]
  println! "{bool}.substitute [{bool} → {int}] = {sub}"

/-- info: version = `1.2.1` -/
#guard_msgs in #eval cvc5.runIO do
  let solver ← Solver.new
  let version ← solver.getVersion
  println! "version = `{version}`"

/--
info: b1 = `b1`
b2 = `b2`
b1_and_b2 = `(and b1 b2)`
b3 = `b3`
b4 = `b4`
conj = `(and b1 b2 b3 b4)`
-/
#guard_msgs in #eval cvc5.runIO do
  let bool ← Srt.Boolean
  let solver ← Solver.new
  let b1 ← solver.declareFun "b1" #[] bool
  println! "b1 = `{b1}`"
  let b2 ← solver.declareFun "b2" #[] bool
  println! "b2 = `{b2}`"
  let b1_and_b2 ← Term.mk .AND #[b1, b2]
  println! "b1_and_b2 = `{b1_and_b2}`"
  let b3 ← solver.declareFun "b3" #[] bool
  println! "b3 = `{b3}`"
  let b4 ← solver.declareFun "b4" #[] bool
  println! "b4 = `{b4}`"
  let conj ← b1.mkInto .AND #[b2, b3, b4]
  println! "conj = `{conj}`"

/-- error: expecting a Boolean subexpression -/
#guard_msgs in #eval cvc5.runIO do
  let bool ← Srt.Boolean
  let int ← Srt.Integer
  let solver ← Solver.new
  let b1 ← solver.declareFun "b1" #[] bool
  let i1 ← solver.declareFun "i1" #[] int
  let shouldFail ← b1.and i1
  cvc5.throw s!"should have failed: `{shouldFail}`"
  return ()

/-- info:
b1_and_b1 = (and b1 b1)
b1_and_b1_simplified = b1
i1_plus_zero = (+ i1 0)
i1_plus_zero_simplified = i1
-/
#guard_msgs in #eval cvc5.runIO do
  let bool ← Srt.Boolean
  let int ← Srt.Integer
  let solver ← Solver.new

  solver.setOption "produce-models" "true"
  solver.setLogic "QF_LIA"

  let b1 ← solver.declareFun "b1" #[] bool
  let b1_and_b1 ← b1.mkInto .AND #[b1]
  println! "b1_and_b1 = {b1_and_b1}"
  let b1_and_b1_simplified ← solver.simplify b1_and_b1
  println! "b1_and_b1_simplified = {b1_and_b1_simplified}"

  let i1 ← solver.declareFun "i1" #[] int
  let i1_plus_zero ← i1.mkInto .ADD #[← Term.mkInteger 0]
  println! "i1_plus_zero = {i1_plus_zero}"
  let i1_plus_zero_simplified ← solver.simplify i1_plus_zero
  println! "i1_plus_zero_simplified = {i1_plus_zero_simplified}"

/-- info:
confirmed unsat
confirmed unsat
confirmed sat
confirmed sat
-/
#guard_msgs in #eval cvc5.runIO do
  let bool ← Srt.Boolean
  let solver ← Solver.new
  let b1 ← solver.declareFun "b1" #[] bool
  let not_b1 ← b1.mkInto .NOT

  solver.assertFormula b1
  let res ← solver.checkSatAssuming #[not_b1]
  if ¬ res.isUnsat then
    cvc5.throw "expected unsat"
  println! "confirmed unsat"
  solver.assertFormula not_b1
  let res ← solver.checkSat
  if ¬ res.isUnsat then
    cvc5.throw "expected unsat"
  println! "confirmed unsat"

  solver.resetAssertions
  let res ← solver.checkSat
  if ¬ res.isSat then
    cvc5.throw "expected sat"
  println! "confirmed sat"
  let res ← solver.checkSatAssuming #[not_b1]
  if ¬ res.isSat then
    cvc5.throw "expected sat"
  println! "confirmed sat"

  return ()


/-- info:
can't retrieve a symbol created by `parseCommands`
-/
#guard_msgs in #eval cvc5.runIO do
  let solver ← Solver.new
  solver.parseSmtLib "\
(set-logic QF_LIA)
(set-option :produce-models true)

(declare-fun b1 () Bool)
(declare-fun b2 () Bool)

(assert (and b1 b2))
  "
  let res ← solver.checkSat
  if ¬ res.isSat then
    cvc5.throw "expected sat"

  let bool ← Srt.Boolean
  let b1 ← solver.declareFun "b1" #[] bool (fresh := false)
  solver.assertFormula (← b1.mkInto .NOT)
  let res ← solver.checkSat
  if ¬ res.isSat then cvc5.throw "it works"
  else println! "can't retrieve a symbol created by `parseCommands`"


/-- info:
`(and b1 b2)` sat
unsat after adding `(not b1)`
-/
#guard_msgs in #eval cvc5.runIO do
  let solver ← Solver.new
  let b1_and_b2 := "(and b1 b2)"
  solver.parseSmtLib s!"\
(set-logic QF_LIA)
(set-option :produce-models true)

(declare-fun b1 () Bool)
(declare-fun b2 () Bool)

(assert {b1_and_b2})
  "
  let res ← solver.checkSat
  if ¬ res.isSat
  then cvc5.throw "expected sat"
  else println! "`{b1_and_b2}` sat"

  let not_b1 := "(not b1)"
  solver.parseSmtLib s!"(assert {not_b1})"
  let res ← solver.checkSat
  if ¬ res.isUnsat
  then cvc5.throw "expected unsat"
  else println! "unsat after adding `{not_b1}`"

/-- error:
[parsing] Error in option parsing: Argument 'bad' for bool option produce-models is not a bool constant

```output
(error "Error in option parsing: Argument 'bad' for bool option produce-models is not a bool constant")
```
-/
#guard_msgs in #eval cvc5.runIO do
  let solver ← Solver.new
  solver.parseSmtLib s!"\
(set-logic QF_LIA)
(set-option :produce-models bad)
  "

/-- error:
Subexpressions must have the same type:
Equation: (= b i)
Type 1: Bool
Type 2: Int
-/
#guard_msgs in #eval cvc5.runIO do
  let solver ← Solver.new
  solver.parseSmtLib s!"\
(set-logic QF_LIA)
(set-option :produce-models true)

(declare-fun b () Bool)
(declare-fun i () Int)

(assert (= b i))
  "

/-- error:
[parsing] cannot get model unless after a SAT or UNKNOWN response.

```output
unsat
(error "cannot get model unless after a SAT or UNKNOWN response.")
```
-/
#guard_msgs in #eval cvc5.runIO do
  let solver ← Solver.new
  solver.parseSmtLib s!"\
(set-logic QF_LIA)
(set-option :produce-models true)

(declare-fun b () Bool)

(assert (and b (not b)))

(check-sat)
(get-model)
  "
