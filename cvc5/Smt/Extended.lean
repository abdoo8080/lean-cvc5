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



-- @[inherit_doc Term.Manager.mkSort]
-- def mkSort (α : Type) [ToCvc5Sort α] : SmtT m cvc5.Sort :=
--   termManagerDo fun tm => tm.mkSort α

-- @[inherit_doc Term.Manager.mkSortBool]
-- def mkSortBool : SmtT m cvc5.Sort :=
--   mkSort Bool

-- @[inherit_doc Term.Manager.mkSortInt]
-- def mkSortInt : SmtT m cvc5.Sort :=
--   mkSort Int

-- @[inherit_doc Term.Manager.mkSortReal]
-- def mkSortReal : SmtT m cvc5.Sort :=
--   mkSort Lean.Rat

-- @[inherit_doc Term.Manager.mkSortRegExp]
-- def mkSortRegExp : SmtT m cvc5.Sort :=
--   termManagerDo fun tm => tm.mkSortRegExp

-- @[inherit_doc Term.Manager.mkSortString]
-- def mkSortString : SmtT m cvc5.Sort :=
--   mkSort String

-- @[inherit_doc Term.Manager.mkSortArray]
-- def mkSortArray (α : Type) [ToCvc5Sort α] : SmtT m cvc5.Sort :=
--   mkSort (Array α)

-- @[inherit_doc Term.Manager.mkSortBitVec]
-- def mkSortBitVec (size : Nat) : SmtT m cvc5.Sort :=
--   mkSort (BitVec size)




-- /-! ## `Solver` monadic functions -/

-- @[inherit_doc Solver.getVersion]
-- def getVersion : SmtT m String :=
--   Solver.getVersion
--   |> solverRun

-- @[inherit_doc Solver.setOption]
-- def setOption (option value : String) : SmtT m Unit :=
--   Solver.setOption option value
--   |> solverRun

-- @[inherit_doc Solver.setLogic]
-- def setLogic (logic : String) : SmtT m Unit :=
--   Solver.setLogic logic
--   |> solverRun

-- @[inherit_doc Solver.getOption]
-- def getOption (option : String) : SmtT m String :=
--   Solver.getOption option
--   |> solverRun

-- @[inherit_doc Solver.assertFormula]
-- def assertFormula (term : Term) : SmtT m Unit :=
--   Solver.assertFormula term
--   |> solverRun

-- @[inherit_doc Solver.checkSat]
-- def checkSat : SmtT m Result :=
--   Solver.checkSat
--   |> solverRun

-- @[inherit_doc Solver.getProof]
-- def getProof : SmtT m (Array Proof) :=
--   Solver.getProof
--   |> solverRun

-- @[inherit_doc Solver.proofToString]
-- def proofToString (proof : Proof) : SmtT m String :=
--   Solver.proofToString proof
--   |> solverRun

-- @[inherit_doc Solver.parse]
-- def parse (smtLib : String) : SmtT m Unit :=
--   Solver.parse smtLib
--   |> solverRun



-- @[inherit_doc Solver.declareFun]
-- def declareFun
--   (symbol : String)
--   (in_sorts : Array cvc5.Sort) (out_sort : cvc5.Sort)
--   (fresh : Bool := false)
-- : SmtT m Term :=
--   Solver.declareFun symbol in_sorts out_sort fresh
--   |> solverRun

-- @[inherit_doc Solver.declareFreshFun]
-- def declareFreshFun
--   (symbol : String) (in_sorts : Array cvc5.Sort) (out_sort : cvc5.Sort)
-- : SmtT m Term :=
--   Solver.declareFreshFun symbol in_sorts out_sort
--   |> solverRun

-- def declareConst (symbol : String) (α : Type) [ToCvc5Sort α] : SmtT m Term := do
--   let sort ← mkSort α
--   declareFun symbol #[] sort

-- @[inherit_doc Solver.declareSort]
-- def declareSort
--   (symbol : String) (arity: Nat) (fresh : Bool := false)
-- : SmtT m Sort :=
--   Solver.declareSort symbol arity fresh
--   |> solverRun

-- @[inherit_doc Solver.declareFreshSort]
-- def declareFreshSort (symbol : String) (arity : Nat) : SmtT m Sort :=
--   Solver.declareFreshSort symbol arity
--   |> solverRun



-- @[inherit_doc Solver.getAssertions]
-- def getAssertions : SmtT m (Array Term) :=
--   Solver.getAssertions
--   |> solverRun

-- @[inherit_doc Solver.getUnsatAssumptions]
-- def getUnsatAssumptions : SmtT m (Array Term) :=
--   Solver.getUnsatAssumptions
--   |> solverRun

-- @[inherit_doc Solver.getUnsatCore]
-- def getUnsatCore : SmtT m (Array Term) :=
--   Solver.getUnsatCore
--   |> solverRun

-- @[inherit_doc Solver.getUnsatCoreLemmas]
-- def getUnsatCoreLemmas : SmtT m (Array Term) :=
--   Solver.getUnsatCoreLemmas
--   |> solverRun

-- @[inherit_doc Solver.getInfo]
-- def getInfo (flag : String) : SmtT m String :=
--   Solver.getInfo flag
--   |> solverRun

-- @[inherit_doc Solver.getOptionNames]
-- def getOptionNames : SmtT m (Array String) :=
--   Solver.getOptionNames
--   |> solverRun



-- @[inherit_doc Solver.getValue]
-- def getValue (term : Term) : SmtT m Term :=
--   Solver.getValue term
--   |> solverRun

-- @[inherit_doc Solver.getValues]
-- def getValues (terms : Array Term) : SmtT m (Array Term) :=
--   Solver.getValues terms
--   |> solverRun



-- @[inherit_doc Solver.resetAssertions]
-- def resetAssertions : SmtT m Unit :=
--   Solver.resetAssertions
--   |> solverRun
