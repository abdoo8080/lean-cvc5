/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import cvc5.Solver.Basic



namespace cvc5

/-- A cvc5 context: a `Term.Manager` and a `Solver`. -/
structure Smt where private mkRaw ::
  private termManager : Term.Manager
  private solver : Solver

/-- Cvc5 context error-state monad transformer. -/
abbrev SmtT m := ExceptT Error (StateT Smt m)

/-- Cvc5 context errot-state IO monad. -/
abbrev SmtM := SmtT IO



namespace Smt

/-- Constructor from a term manager. -/
def ofTermManager (tm : Term.Manager) : Smt :=
  ⟨tm, Solver.mk tm⟩

/-- Constructor. -/
def mk [Monad m] [MonadLiftT BaseIO m] : m Smt := do
  let tm ← Term.Manager.mk
  return ofTermManager tm

/-- Runs some monadic `Smt` code given a term manager. -/
def runWith [instMonad : Monad m]
  (tm : Term.Manager)
  (code : SmtT m α)
: ExceptT Error m α := do
  let smt := ofTermManager tm
  match ← code smt with
  | (.ok res, _) => instMonad.pure (.ok res)
  | (.error err, _) => instMonad.pure (.error err)

/-- Runs some monadic `Smt` code given a term manager, with error-handling. -/
def runWithOr [Monad m]
  (tm : Term.Manager)
  (code : SmtT m α)
  (handleError : Error → m α)
: m α := do
  match ← runWith tm code with
  | Except.ok res => return res
  | .error err => handleError err

/-- Runs some monadic `Smt` code given a term manager, panics on errors. -/
def runWith! [Monad m] [Inhabited α]
  (tm : Term.Manager)
  (code : SmtT m α)
  (handleError : Error → m α := fun e => panic! s!"[cvc5.Smt] {e}")
: m α := do
  match ← runWith tm code with
  | Except.ok res => return res
  | .error err => handleError err

/-- Runs some monadic `Smt` code. -/
def run
  [instMonad : Monad m] [MonadLiftT BaseIO m]
  (code : SmtT m α)
: ExceptT Error m α := do
  let smt ← mk
  match ← code smt with
  | (.ok res, _) => instMonad.pure (.ok res)
  | (.error err, _) => instMonad.pure (.error err)

/-- Runs some monadic `Smt` code, with error-handling. -/
def runOr [Monad m] [MonadLiftT BaseIO m]
  (code : SmtT m α)
  (handleError : Error → m α)
: m α := do
  match ← run code with
  | Except.ok res => return res
  | .error err => handleError err

/-- Runs some monadic `Smt` code but panics on errors. -/
def run! [Monad m] [MonadLiftT BaseIO m] [Inhabited α]
  (code : SmtT m α)
  (handleError : Error → m α := fun e => panic! s!"[cvc5.Smt] {e}")
: m α :=
  runOr code handleError



variable [instMonad : Monad m]



def solverRun (code : SolverT m α) : SmtT m α :=
  fun smt => do
    let (res, solver) ← code smt.solver
    return (res, {smt with solver})

instance instMonadLiftSolverT : MonadLift (SolverT m) (SmtT m) :=
  ⟨solverRun⟩



/-! ## `Term.Manager`/`Solver` access and manipulation -/

private def getTerm.Manager : SmtT m Term.Manager :=
  fun smt => return (.ok smt.termManager, smt)

def termManagerDoM (f : Term.Manager → SmtT m α) : SmtT m α :=
  fun smt => f smt.termManager smt

def termManagerDo (f : Term.Manager → α) : SmtT m α :=
  fun smt => return (.ok <| f smt.termManager, smt)

private def getSolver : SmtT m Solver :=
  fun smt => return (.ok smt.solver, smt)



/-! ## `Term.Manager` monadic functions -/

@[inherit_doc Term.Manager.mkBoolean]
def mkBool (b : Bool) : SmtT m Term :=
  termManagerDo fun tm => tm.mkBoolean b

@[inherit_doc Term.Manager.mkInteger]
def mkInt (i : Int) : SmtT m Term :=
  termManagerDo fun tm => tm.mkInteger i

@[inherit_doc Term.Manager.mkTerm]
def mkTerm (k : Kind) (kids : Array Term := #[]) : SmtT m Term :=
  termManagerDo fun tm => tm.mkTerm k kids



@[inherit_doc Term.Manager.mkSortBool]
def mkSortBool : SmtT m cvc5.Sort :=
  termManagerDo fun tm => tm.mkSortBool

@[inherit_doc Term.Manager.mkSortInt]
def mkSortInt : SmtT m cvc5.Sort :=
  termManagerDo fun tm => tm.mkSortInt

@[inherit_doc Term.Manager.mkSortReal]
def mkSortReal : SmtT m cvc5.Sort :=
  termManagerDo fun tm => tm.mkSortReal

@[inherit_doc Term.Manager.mkSortRegExp]
def mkSortRegExp : SmtT m cvc5.Sort :=
  termManagerDo fun tm => tm.mkSortRegExp

@[inherit_doc Term.Manager.mkSortString]
def mkSortString : SmtT m cvc5.Sort :=
  termManagerDo fun tm => tm.mkSortString

@[inherit_doc Term.Manager.mkSortArray]
def mkSortArray (idx sort : cvc5.Sort) : SmtT m cvc5.Sort :=
  termManagerDo fun tm => tm.mkSortArray idx sort

@[inherit_doc Term.Manager.mkSortBitVec]
def mkSortBitVec (size : Nat) : SmtT m cvc5.Sort :=
  termManagerDo fun tm => tm.mkSortBitVec size




/-! ## `Solver` monadic functions -/

@[inherit_doc Solver.getVersion]
def getVersion : SmtT m String :=
  Solver.getVersion
  |> solverRun

@[inherit_doc Solver.setOption]
def setOption (option value : String) : SmtT m Unit :=
  Solver.setOption option value
  |> solverRun

@[inherit_doc Solver.setLogic]
def setLogic (logic : String) : SmtT m Unit :=
  Solver.setLogic logic
  |> solverRun

@[inherit_doc Solver.getOption]
def getOption (option : String) : SmtT m String :=
  Solver.getOption option
  |> solverRun

@[inherit_doc Solver.assertFormula]
def assertFormula (term : Term) : SmtT m Unit :=
  Solver.assertFormula term
  |> solverRun

@[inherit_doc Solver.checkSat]
def checkSat : SmtT m Result :=
  Solver.checkSat
  |> solverRun

@[inherit_doc Solver.getProof]
def getProof : SmtT m (Array Proof) :=
  Solver.getProof
  |> solverRun

@[inherit_doc Solver.proofToString]
def proofToString (proof : Proof) : SmtT m String :=
  Solver.proofToString proof
  |> solverRun

@[inherit_doc Solver.parse]
def parse (smtLib : String) : SmtT m Unit :=
  Solver.parse smtLib
  |> solverRun



@[inherit_doc Solver.declareFun]
def declareFun
  (symbol : String)
  (in_sorts : Array cvc5.Sort) (out_sort : cvc5.Sort)
  (fresh : Bool := false)
: SmtT m Term :=
  Solver.declareFun symbol in_sorts out_sort fresh
  |> solverRun

@[inherit_doc Solver.declareFreshFun]
def declareFreshFun
  (symbol : String) (in_sorts : Array cvc5.Sort) (out_sort : cvc5.Sort)
: SmtT m Term :=
  Solver.declareFreshFun symbol in_sorts out_sort
  |> solverRun

@[inherit_doc Solver.declareSort]
def declareSort
  (symbol : String) (arity: Nat) (fresh : Bool := false)
: SmtT m Sort :=
  Solver.declareSort symbol arity fresh
  |> solverRun

@[inherit_doc Solver.declareFreshSort]
def declareFreshSort (symbol : String) (arity : Nat) : SmtT m Sort :=
  Solver.declareFreshSort symbol arity
  |> solverRun



@[inherit_doc Solver.getAssertions]
def getAssertions : SmtT m (Array Term) :=
  Solver.getAssertions
  |> solverRun

@[inherit_doc Solver.getUnsatAssumptions]
def getUnsatAssumptions : SmtT m (Array Term) :=
  Solver.getUnsatAssumptions
  |> solverRun

@[inherit_doc Solver.getUnsatCore]
def getUnsatCore : SmtT m (Array Term) :=
  Solver.getUnsatCore
  |> solverRun

@[inherit_doc Solver.getUnsatCoreLemmas]
def getUnsatCoreLemmas : SmtT m (Array Term) :=
  Solver.getUnsatCoreLemmas
  |> solverRun

@[inherit_doc Solver.getInfo]
def getInfo (flag : String) : SmtT m String :=
  Solver.getInfo flag
  |> solverRun

@[inherit_doc Solver.getOptionNames]
def getOptionNames : SmtT m (Array String) :=
  Solver.getOptionNames
  |> solverRun



@[inherit_doc Solver.getValue]
def getValue (term : Term) : SmtT m Term :=
  Solver.getValue term
  |> solverRun

@[inherit_doc Solver.getValues]
def getValues (terms : Array Term) : SmtT m (Array Term) :=
  Solver.getValues terms
  |> solverRun



@[inherit_doc Solver.resetAssertions]
def resetAssertions : SmtT m Unit :=
  Solver.resetAssertions
  |> solverRun
