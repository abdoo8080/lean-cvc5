/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Adrien Champion
-/

import cvc5Test.Init

/-! # Black box testing of the `Solver` type

- <https://github.com/cvc5/cvc5/blob/main/test/unit/api/cpp/api_solver_black.cpp>
-/

namespace cvc5.Test

/-! # Synthesis/sygus -/

test![TestApiBlackSolver, declareSygusVar] tm => do
  let solver ← Solver.new tm
  solver.setOption "sygus" "true"
  let bool ← tm.getBooleanSort
  let int ← tm.getIntegerSort
  let funSort ← tm.mkFunctionSort #[int] bool
  let nullSort := cvc5.Sort.null ()

  solver.declareSygusVar "" bool |> assertOkDiscard
  solver.declareSygusVar "" funSort |> assertOkDiscard
  solver.declareSygusVar "b" bool |> assertOkDiscard
  solver.declareSygusVar "" nullSort |> assertError
    "invalid null argument for 'sort'"
  solver.declareSygusVar "a" nullSort |> assertError
    "invalid null argument for 'sort'"

  (← Solver.new tm).declareSygusVar "" bool |> assertError
    "cannot call declareSygusVar unless sygus is enabled (use --sygus)"

  let tm' ← TermManager.new
  let solver' ← Solver.new tm'
  solver'.setOption "sygus" "true"
  solver'.declareSygusVar "" bool |> assertError
    "Given sort is not associated with the term manager of this solver"

test![TestApiBlackSolver, declareSygusVar] tm => do
  let solver ← Solver.new tm
  let nullTerm := Term.null ()
  let boolTerm ← tm.mkBoolean true
  let bool ← tm.getBooleanSort
  let int ← tm.getIntegerSort
  let boolVar ← tm.mkVar bool
  let intVar ← tm.mkVar int

  solver.mkGrammar #[] #[intVar] |> assertOkDiscard
  solver.mkGrammar #[boolVar] #[intVar] |> assertOkDiscard
  solver.mkGrammar #[] #[] |> assertError
    "invalid size of argument 'ntSymbols', expected a non-empty vector"
  solver.mkGrammar #[] #[nullTerm] |> assertError
    "invalid null term in 'ntSymbols' at index 0"
  solver.mkGrammar #[] #[boolTerm] |> assertError
    "invalid bound variable in 'ntSymbols' at index 0, expected a bound variable"
  solver.mkGrammar #[boolTerm] #[intVar] |> assertError
    "invalid bound variable in 'boundVars' at index 0, expected a bound variable"

  let tm' ← TermManager.new
  let solver' ← Solver.new tm'
  let boolVar' ← tm'.mkVar (← tm'.getBooleanSort)
  let intVar' ← tm'.mkVar (← tm'.getIntegerSort)
  solver'.mkGrammar #[boolVar'] #[intVar'] |> assertOkDiscard
  solver'.mkGrammar #[boolVar] #[intVar'] |> assertError
    "invalid term in 'boundVars' at index 0, \
    expected a term associated with the term manager of this solver"
  solver'.mkGrammar #[boolVar'] #[intVar] |> assertError
    "invalid term in 'ntSymbols' at index 0, \
    expected a term associated with the term manager of this solver"

test![TestApiBlackSolver, synthFun] tm => do
  let solver ← Solver.new tm
  solver.setOption "sygus" "true"
  let bool ← tm.getBooleanSort
  let int ← tm.getIntegerSort
  let fls ← tm.mkBoolean false
  let nullTerm := Term.null ()
  let term ← tm.mkVar bool "term"
  let start1 ← tm.mkVar bool "start1"
  let start2 ← tm.mkVar int "start2"

  let mut g1 ← solver.mkGrammar #[term] #[start1]
  solver.synthFun "" #[] bool |> assertOkDiscard
  solver.synthFun "f1" #[term] bool |> assertOkDiscard
  solver.synthFun "f2" #[term] bool g1 |> assertError
    "invalid grammar, must have at least one rule for each non-terminal symbol"
  g1 ← g1.addRule start1 fls

  let mut g2 ← solver.mkGrammar #[term] #[start2]
  g2 ← g2.addRule start2 (← tm.mkInteger 0)

  solver.synthFun "" #[] bool |> assertOkDiscard
  solver.synthFun "f1" #[term] bool |> assertOkDiscard
  solver.synthFun "f2" #[term] bool g1 |> assertOkDiscard

  solver.synthFun "f3" #[nullTerm] bool |> assertError
    "invalid null term in 'boundVars' at index 0"
  solver.synthFun "f4" #[term] (Sort.null ()) |> assertError
    "invalid null argument for 'sort'"
  solver.synthFun "f6" #[term] bool g2 |> assertError
    "invalid Start symbol for grammar, expected Start's sort to be Bool but found Int"

  let tm2 ← TermManager.new
  let solver2 ← Solver.new tm2
  solver2.setOption "sygus" "true"
  let bool2 ← tm2.getBooleanSort
  let term2 ← tm2.mkVar bool2 "term2"
  solver2.synthFun "f1" #[term2] bool |> assertError
    "Given sort is not associated with the term manager of this solver"
  solver2.synthFun "" #[] bool |> assertError
    "Given sort is not associated with the term manager of this solver"
  solver2.synthFun "f1" #[term] bool2 |> assertError
    "invalid term in 'boundVars' at index 0, \
    expected a term associated with the term manager of this solver"

test![TestApiBlackSolver, addSygusConstraint] tm => do
  let solver ← Solver.new tm
  solver.setOption "sygus" "true"
  let nullTerm := Term.null ()
  let boolTerm ← tm.mkBoolean true
  let intTerm ← tm.mkInteger 1

  solver.addSygusConstraint boolTerm |> assertOk
  solver.addSygusConstraint nullTerm |> assertError
    "invalid null argument for 'term'"
  solver.addSygusConstraint intTerm |> assertError
    "invalid argument '1' for 'term', expected boolean term"

  let tm2 ← TermManager.new
  let solver2 ← Solver.new tm2
  solver2.setOption "sygus" "true"
  solver2.addSygusConstraint boolTerm |> assertError
    "Given term is not associated with the term manager of this solver"

test![TestApiBlackSolver, getSygusConstraints] tm => do
  let solver ← Solver.new tm
  solver.setOption "sygus" "true"
  let tru ← tm.mkBoolean true
  let fls ← tm.mkBoolean false
  solver.addSygusConstraint tru
  solver.addSygusConstraint fls
  assertEq (← solver.getSygusConstraints) #[tru, fls]

test![TestApiBlackSolver, addSygusAssume] tm => do
  let solver ← Solver.new tm
  solver.setOption "sygus" "true"
  let nullTerm := Term.null ()
  let boolTerm ← tm.mkBoolean true
  let intTerm ← tm.mkInteger 1

  solver.addSygusAssume boolTerm |> assertOk
  solver.addSygusAssume nullTerm |> assertError
    "invalid null argument for 'term'"
  solver.addSygusAssume intTerm |> assertError
    "invalid argument '1' for 'term', expected boolean term"

  let tm2 ← TermManager.new
  let solver2 ← Solver.new tm2
  solver2.setOption "sygus" "true"
  solver2.addSygusAssume boolTerm |> assertError
    "Given term is not associated with the term manager of this solver"

test![TestApiBlackSolver, getSygusAssumptions] tm => do
  let solver ← Solver.new tm
  solver.setOption "sygus" "true"
  let tru ← tm.mkBoolean true
  let fls ← tm.mkBoolean false
  solver.addSygusAssume tru
  solver.addSygusAssume fls
  assertEq (← solver.getSygusAssumptions) #[tru, fls]

test![TestApiBlackSolver, getSygusAssumptions] tm => do
  let solver ← Solver.new tm
  solver.setOption "sygus" "true"
  let nullTerm := Term.null ()
  let intTerm ← tm.mkInteger 1
  let bool ← tm.getBooleanSort
  let real ← tm.getRealSort

  let inv ← solver.declareFun "inv" #[real] bool
  let pre ← solver.declareFun "pre" #[real] bool
  let trans ← solver.declareFun "trans" #[real, real] bool
  let post ← solver.declareFun "trans" #[real] bool

  let inv1 ← solver.declareFun "inv1" #[real] real

  let trans1 ← solver.declareFun "trans1" #[bool, real] bool
  let trans2 ← solver.declareFun "trans2" #[real, bool] bool
  let trans3 ← solver.declareFun "trans3" #[real, real] real

  solver.addSygusInvConstraint inv pre trans post |> assertOk

  solver.addSygusInvConstraint nullTerm pre trans post |> assertError
    "invalid null argument for 'inv'"
  solver.addSygusInvConstraint inv nullTerm trans post |> assertError
    "invalid null argument for 'pre'"
  solver.addSygusInvConstraint inv pre nullTerm post |> assertError
    "invalid null argument for 'trans'"
  solver.addSygusInvConstraint inv pre trans nullTerm |> assertError
    "invalid null argument for 'post'"

  solver.addSygusInvConstraint inv1 pre trans post |> assertError
    "invalid argument 'inv1' for 'inv', expected boolean range"

  solver.addSygusInvConstraint inv trans trans post |> assertError
    "expected inv and pre to have the same sort"

  solver.addSygusInvConstraint inv pre intTerm post |> assertError
    "expected the sort of trans sort to be (-> Real Bool)"
  solver.addSygusInvConstraint inv pre pre post |> assertError
    "expected the sort of trans sort to be (-> Real Bool)"
  solver.addSygusInvConstraint inv pre trans1 post |> assertError
    "expected the sort of trans sort to be (-> Real Bool)"
  solver.addSygusInvConstraint inv pre trans2 post |> assertError
    "expected the sort of trans sort to be (-> Real Bool)"
  solver.addSygusInvConstraint inv pre trans3 post |> assertError
    "expected the sort of trans sort to be (-> Real Bool)"

  solver.addSygusInvConstraint inv pre trans trans |> assertError
    "expected inv and post to have the same sort"

  let tm' ← TermManager.new
  let solver' ← Solver.new tm'
  solver'.setOption "sygus" "true"
  let bool' ← tm'.getBooleanSort
  let real' ← tm'.getRealSort
  let inv' ← solver'.declareFun "inv" #[real'] bool'
  let pre' ← solver'.declareFun "inv" #[real'] bool'
  let trans' ← solver'.declareFun "inv" #[real', real'] bool'
  let post' ← solver'.declareFun "inv" #[real'] bool'
  solver'.addSygusInvConstraint inv' pre' trans' post' |> assertOk
  solver'.addSygusInvConstraint inv pre' trans' post' |> assertError
    "Given term is not associated with the term manager of this solver"
  solver'.addSygusInvConstraint inv' pre trans' post' |> assertError
    "Given term is not associated with the term manager of this solver"
  solver'.addSygusInvConstraint inv' pre' trans post' |> assertError
    "Given term is not associated with the term manager of this solver"
  solver'.addSygusInvConstraint inv' pre' trans' post |> assertError
    "Given term is not associated with the term manager of this solver"

test![TestApiBlackSolver, checkSynth] tm => do
  let solver ← Solver.new tm
  solver.setOption "sygus" "true"
  solver.checkSynth |> assertOkDiscard

test![TestApiBlackSolver, getSynthSolution] tm => do
  let solver ← Solver.new tm
  solver.setOption "sygus" "true"
  solver.setOption "incremental" "false"

  let nullTerm := Term.null ()
  let fls ← tm.mkBoolean false
  let bool ← tm.getBooleanSort
  let f ← solver.synthFun "f" #[] bool

  solver.getSynthSolution f |> assertError
    "solver is not in a state immediately preceded by a successful call to checkSynth"

  let synthRes ← solver.checkSynth
  assertTrue synthRes.hasSolution

  solver.getSynthSolution f |> assertOkDiscard
  solver.getSynthSolution f |> assertOkDiscard

  solver.getSynthSolution nullTerm |> assertError
    "invalid null argument for 'term'"
  solver.getSynthSolution fls |> assertError
    "synthesis solution not found for given term"

  (← Solver.new tm).getSynthSolution f |> assertError
    "solver is not in a state immediately preceded by a successful call to checkSynth"

test![TestApiBlackSolver, getSynthSolutions] tm => do
  let solver ← Solver.new tm
  solver.setOption "sygus" "true"
  solver.setOption "incremental" "false"

  let nullTerm := Term.null ()
  let fls ← tm.mkBoolean false
  let bool ← tm.getBooleanSort
  let f ← solver.synthFun "f" #[] bool

  solver.getSynthSolutions #[] |> assertError
    "invalid size of argument 'terms', expected non-empty vector"
  solver.getSynthSolutions #[f] |> assertError
    "solver is not in a state immediately preceded by a successful call to checkSynth"

  let synthRes ← solver.checkSynth
  assertTrue synthRes.hasSolution

  solver.getSynthSolutions #[f] |> assertOkDiscard
  solver.getSynthSolutions #[f] |> assertOkDiscard

  solver.getSynthSolutions #[] |> assertError
    "invalid size of argument 'terms', expected non-empty vector"
  solver.getSynthSolutions #[nullTerm] |> assertError
    "invalid null term in 'terms' at index 0"
  solver.getSynthSolutions #[fls] |> assertError
    "synthesis solution not found for term at index 0"

  (← Solver.new tm).getSynthSolutions #[f] |> assertError
    "solver is not in a state immediately preceded by a successful call to checkSynth"

test![TestApiBlackSolver, checkSynthNext] tm => do
  let solver ← Solver.new tm
  solver.setOption "sygus" "true"
  solver.setOption "incremental" "true"
  let bool ← tm.getBooleanSort
  let f ← solver.synthFun "f" #[] bool

  let synthRes ← solver.checkSynth
  assertTrue synthRes.hasSolution
  solver.getSynthSolutions #[f] |> assertOkDiscard
  let synthRes ← solver.checkSynthNext
  assertTrue synthRes.hasSolution
  solver.getSynthSolutions #[f] |> assertOkDiscard

test![TestApiBlackSolver, checkSynthNext2] tm => do
  let solver ← Solver.new tm
  solver.setOption "sygus" "true"
  solver.setOption "incremental" "false"
  let bool ← tm.getBooleanSort
  let _f ← solver.synthFun "f" #[] bool
  solver.checkSynth |> assertOkDiscard
  solver.checkSynthNext |> assertError
    "cannot check for a next synthesis solution when not solving incrementally (use --incremental)"

test![TestApiBlackSolver, checkSynthNext3] tm => do
  let solver ← Solver.new tm
  solver.setOption "sygus" "true"
  solver.setOption "incremental" "true"
  let bool ← tm.getBooleanSort
  let _f ← solver.synthFun "f" #[] bool
  solver.checkSynthNext |> assertError
    "Cannot check-synth-next unless immediately preceded \
    by a successful call to check-synth(-next)."

test![TestApiBlackSolver, findSynth] tm => do
  let solver ← Solver.new tm
  solver.setOption "sygus" "true"
  let bool ← tm.getBooleanSort
  let start ← tm.mkVar bool
  let mut grammar ← solver.mkGrammar #[] #[start]
  solver.synthFun "f" #[] bool grammar |> assertError
    "invalid grammar, must have at least one rule for each non-terminal symbol"

  let tru ← tm.mkBoolean true
  let fls ← tm.mkBoolean false
  grammar ← grammar.addRule start tru
  grammar ← grammar.addRule start fls
  let _f ← solver.synthFun "f" #[] bool grammar

  -- should enumerate based on the grammar of the function to synthesize above
  let term ← solver.findSynth .ENUM
  assertFalse term.isNull
  assertTrue term.getSort.isBoolean

test![TestApiBlackSolver, findSynth2] tm => do
  let solver ← Solver.new tm
  solver.setOption "sygus" "true"
  solver.setOption "incremental" "true"
  let bool ← tm.getBooleanSort
  let start ← tm.mkVar bool
  let mut grammar ← solver.mkGrammar #[] #[start]
  let tru ← tm.mkBoolean true
  let fls ← tm.mkBoolean false
  grammar ← grammar.addRule start tru
  grammar ← grammar.addRule start fls

  -- should enumerate true/false
  let term ← solver.findSynth .ENUM grammar
  assertFalse term.isNull
  assertTrue term.getSort.isBoolean
  let term ← solver.findSynthNext
  assertFalse term.isNull
  assertTrue term.getSort.isBoolean
