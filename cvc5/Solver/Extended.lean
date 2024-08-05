/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import cvc5.Init
import cvc5.Term.Extended
import cvc5.Solver.Basic



namespace cvc5.Solver

variable [Monad m]

/-- Sets the solver's logic using `Logic`. -/
def setLogic' (logic : Logic) : SolverT m Unit :=
  setLogic logic.toSmtLib

/-- Declares a nullary function symbol. -/
def declareConst
  (symbol : String) (sort : cvc5.Sort)
  (fresh : Bool := false)
: SolverT m Term := do
  declareFun symbol #[] sort fresh

/-- Returns `true` (`false`) on *sat* (*unsat*), and `none` otherwise.

See also `checkSat`.
-/
def checkSat? : SolverT m (Option Bool) := do
  let res ← checkSat
  if res.isSat then
    return true
  else if res.isUnsat then
    return false
  else
    return none

/-- Parses a string and runs some commands. -/
def parseAnd (smtLib : String) (andThen : SolverT m α) : SolverT m α := do
  parse smtLib
  andThen
