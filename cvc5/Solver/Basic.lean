/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import cvc5.Term.Basic
import cvc5.Proof.Basic



namespace cvc5

private opaque SolverImpl : NonemptyType.{0}

def Solver : Type := SolverImpl.type

instance Solver.instNonemptySolver : Nonempty Solver := SolverImpl.property

/-- `Solver` error-state monad transformer. -/
abbrev SolverT m := ExceptT Error (StateT Solver m)

/-- `Solver` error-state IO monad. -/
abbrev SolverM := SolverT IO



namespace Solver

@[extern "solver_new"]
opaque mk : Term.Manager → Solver



variable [Monad m]



/-- Runs a `SolverT` on a fresh solver. -/
def run (tm : Term.Manager) (query : SolverT m α) : m (Except Error α) := do
  match ← ExceptT.run query (mk tm) with
  | (.ok x, _) => return .ok x
  | (.error e, _) => return .error e

/-- Same as `Solver.run` with an error handler. -/
def runOr
  (tm : Term.Manager)
  (query : SolverT m α)
  (handleError : Error → m α)
: m α := do
  match ← ExceptT.run query (mk tm) with
  | (.ok x, _) => return x
  | (.error e, _) => handleError e

/-- Same as `Solver.run` but panics on errors. -/
def run!
  [Inhabited α]
  (tm : Term.Manager)
  (query : SolverT m α)
  (handleError : Error → m α := fun e => panic! s!"[cvc5.Solver] {e}")
: m α := do
  runOr tm query handleError



@[export solver_val]
private def val (a : α) : SolverT m α := pure a

@[export solver_err]
private def err (e : Error) : SolverT m α := throw e

/-- `String` representation of the version of this solver. -/
@[extern "solver_getVersion"]
opaque getVersion : SolverT m String

/-- Sets the value of a solver option. -/
@[extern "solver_setOption"]
opaque setOption (option value : String) : SolverT m Unit

/-- Sets the solver's logic. -/
@[extern "solver_setLogic"]
opaque setLogic (logic : String) : SolverT m Unit

/-- Get the value associated to a solver option. -/
@[extern "solver_getOption"]
opaque getOption : (option : String) → SolverT m String

/-- Asserts a formula. -/
@[extern "solver_assertFormula"]
opaque assertFormula : Term → SolverT m Unit

/-- Checks satisfiability. -/
@[extern "solver_checkSat"]
opaque checkSat : SolverT m Result

/-- Get a proof associated with the most recent call to a `checkSat`-like function. -/
@[extern "solver_getProof"]
opaque getProof : SolverT m (Array Proof)

/-- Prints a proof as a string, some formatting aspects are decided by solver options.-/
@[extern "solver_proofToString"]
opaque proofToString : Proof → SolverT m String

/-- Parses some SMT-LIB 2.6 commands. -/
@[extern "solver_parse"]
opaque parse : String → SolverT m Unit



/-! ## Symbol declaration -/
section declarations

/-- Declares a function symbol `symbol` with signature `in_sorts → out_sort`.

If `fresh`, then a new (fresh) `Term` is always produced; otherwise, the `Term` will always be
(physically) the same.

See also `declareFreshFun`.
-/
@[extern "solver_declareFun"]
opaque declareFun :
  (symbol : String)
  → (in_sorts : Array cvc5.Sort) → (out_sort : cvc5.Sort)
  → (fresh : Bool)
  → SolverT m Term

/-- Declares a new function symbol `symbol` with signature `in_sorts → out_sort`.

Note that creating functions with the same name and signature will always yield a new, physically
different, `Term`.

See also `declareFun`.
-/
def declareFreshFun
  (symbol : String) (in_sorts : Array cvc5.Sort) (out_sort : cvc5.Sort)
: SolverT m Term :=
  declareFun symbol in_sorts out_sort true

/-- Declares a sort symbol `symbol` with arity `arity`.

If `fresh`, then a new (fresh) `Sort` is always produced; otherwise, the `Sort` will always be
(physically) the same.

See also `declareFreshSort`.
-/
@[extern "solver_declareSort"]
opaque declareSort :
  (symbol : String) → (arity: Nat) → (fresh : Bool) → SolverT m Sort

/-- Declares a new sort symbol `symbol` with arity `arity`.

Note that creating sorts with the same name and arity will always yield a new, physically different,
`Sort`.

See also `declareSort`.
-/
def declareFreshSort (symbol : String) (arity : Nat) : SolverT m Sort :=
  declareSort symbol arity true

end declarations



/-! ## Solver information extraction -/
section information_extraction

/-- Get the asserted formulas. -/
@[extern "solver_getAssertions"]
opaque getAssertions : SolverT m (Array Term)

/-- When `unsat`, retrieves the unsat (*failed*) asserted assumptions.

Note: requires to enable option `produce-unsat-assumptions`.

# TODO

What happens

- when `sat`?
- no `check-sat` has been issued?
-/
@[extern "solver_getUnsatAssumptions"]
opaque getUnsatAssumptions : SolverT m (Array Term)

/-- When `unsat`, retrieves the unsat core.

Note: requires to enable option `produce-unsat-core`.

# TODO

What happens

- when `sat`?
- no `check-sat` has been issued?
-/
@[extern "solver_getUnsatCore"]
opaque getUnsatCore : SolverT m (Array Term)

/-- When `unsat`, retrieves the lemmas used to derive unsatisfiability.

Note: requires the SAT proof unsat core mode: `unsat-core-mode=sat-proof`.

# TODO

What happens

- when `sat`?
- no `check-sat` has been issued?
-/
@[extern "solver_getUnsatCoreLemmas"]
opaque getUnsatCoreLemmas : SolverT m (Array Term)

/-- Get the information associated to a flag. -/
@[extern "solver_getInfo"]
opaque getInfo : (flag : String) → SolverT m String

/-- Get the name of all the solver options. -/
@[extern "solver_getOptionNames"]
opaque getOptionNames : SolverT m (Array String)

end information_extraction



/-! ## Term evaluation in a model -/
section evaluation

/-- Evaluates a term in the current model.

# TODO

What happens

- when `unsat`?
- no `check-sat` has been issued?
-/
@[extern "solver_getValue"]
opaque getValue : (term : Term) → SolverT m Term

/-- Evaluates some terms in the current model. -/
def getValues (terms : Array Term) : SolverT m (Array Term) :=
  Array.mkEmpty terms.size
  |> terms.foldlM fun array term =>
    return array.push (← getValue term)

end evaluation



/-! ## Reset / incrementality -/
section restart_reset

/-- Removes all assertions. -/
@[extern "solver_resetAssertions"]
opaque resetAssertions : SolverT m Unit

end restart_reset
