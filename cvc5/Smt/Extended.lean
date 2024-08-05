/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import cvc5.Smt.Basic
import cvc5.Term.Extended
import cvc5.Solver.Extended



namespace cvc5.Smt

variable [Monad m]



@[inherit_doc Term.Manager.mkSort]
def mkSort (α : Type) [ToCvc5Sort α] : SmtT m cvc5.Sort :=
  termManagerDo fun tm => tm.mkSort α



@[inherit_doc Solver.setLogic']
def setLogic' (l : Logic) : SmtT m Unit :=
  Solver.setLogic' l |> Smt.solverRun

/-- Declares a constant, accepts types that can be converted to cvc5 sorts. -/
def declareConst (symbol : String) (α : Type) [ToCvc5Sort α] : SmtT m Term := do
  let sort ← mkSort α
  declareFun symbol #[] sort

/-- True if *sat*, false if *unsat*, `none` if *unknown*. -/
def checkSat? : SmtT m (Option Bool) := do
  let res ← checkSat
  if res.isSat
  then return true
  else if res.isUnsat
  then return false
  else if res.isUnknown
  then return none
  else panic! s!"`{res} : Result` is neither sat, unsat, or unknown"


@[inherit_doc Term.Manager.mkIte]
def mkIte (cnd thn els : Term) : SmtT m Term :=
  termManagerDo fun tm => tm.mkIte cnd thn els

@[inherit_doc Term.Manager.mkEqualN]
def mkEqualN (terms : Array Term) (h : 1 < terms.size := by simp_arith) : SmtT m Term :=
  termManagerDo fun tm => tm.mkEqualN terms h

@[inherit_doc Term.Manager.mkEqual]
def mkEqual (lft rgt : Term) : SmtT m Term :=
  termManagerDo fun tm => tm.mkEqual lft rgt

@[inherit_doc Term.Manager.mkNot]
def mkNot (t : Term) : SmtT m Term :=
  termManagerDo fun tm => tm.mkNot t

@[inherit_doc Term.Manager.mkImplies]
def mkImplies (lhs rhs : Term) : SmtT m Term :=
  termManagerDo fun tm => tm.mkImplies lhs rhs
