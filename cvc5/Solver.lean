import Std.Data.Rat.Basic

import cvc5.Kind
import cvc5.ProofRule
import cvc5.SkolemId

@[export rat_mk]
private def Rat.mk : Int → Nat → Rat := mkRat

namespace cvc5

private opaque ResultImpl : NonemptyType.{0}

def Result : Type := ResultImpl.type

instance Result.instNonemptyResult : Nonempty Result := ResultImpl.property

private opaque SortImpl : NonemptyType.{0}

end cvc5

def cvc5.Sort : Type := cvc5.SortImpl.type

namespace cvc5

instance Sort.instNonemptySort : Nonempty cvc5.Sort := SortImpl.property

private opaque OpImpl : NonemptyType.{0}

def Op : Type := OpImpl.type

instance Op.instNonemptyOp : Nonempty Op := OpImpl.property

private opaque TermImpl : NonemptyType.{0}

def Term : Type := TermImpl.type

instance Term.instNonemptyTerm : Nonempty Term := TermImpl.property

private opaque ProofImpl : NonemptyType.{0}

def Proof : Type := ProofImpl.type

instance Proof.instNonemptyProof : Nonempty Proof := ProofImpl.property

private opaque TermManagerImpl : NonemptyType.{0}

def TermManager : Type := TermManagerImpl.type

instance TermManager.instNonemptyTermManager : Nonempty TermManager := TermManagerImpl.property

inductive Error where
  | missingValue
  | user_error (msg : String)
deriving Repr

private opaque SolverImpl : NonemptyType.{0}

def Solver : Type := SolverImpl.type

instance Solver.instNonemptySolver : Nonempty Solver := SolverImpl.property

abbrev SolverT m := ExceptT Error (StateT Solver m)

abbrev SolverM := SolverT IO

namespace Result

@[extern "result_isSat"]
opaque isSat : Result → Bool

@[extern "result_isUnsat"]
opaque isUnsat : Result → Bool

@[extern "result_isUnknown"]
opaque isUnknown : Result → Bool

@[extern "result_toString"]
protected opaque toString : Result → String

instance : ToString Result := ⟨Result.toString⟩

end Result

@[extern "sort_null"]
opaque Sort.null : Unit → cvc5.Sort

instance Sort.instInhabitedSort : Inhabited cvc5.Sort := ⟨Sort.null ()⟩

@[extern "sort_getKind"]
opaque Sort.getKind : cvc5.Sort → SortKind

@[extern "sort_getFunctionDomainSorts"]
opaque Sort.getFunctionDomainSorts : cvc5.Sort → Array cvc5.Sort

@[extern "sort_getFunctionCodomainSort"]
opaque Sort.getFunctionCodomainSort : cvc5.Sort → cvc5.Sort

@[extern "sort_getSymbol"]
opaque Sort.getSymbol : cvc5.Sort → String

@[extern "sort_isInteger"]
opaque Sort.isInteger : cvc5.Sort → Bool

@[extern "sort_getBitVectorSize"]
opaque Sort.getBitVectorSize : cvc5.Sort → UInt32

@[extern "sort_toString"]
protected opaque Sort.toString : cvc5.Sort → String

instance Sort.instToStringSort : ToString cvc5.Sort := ⟨Sort.toString⟩

namespace Op

@[extern "op_null"]
opaque null : Unit → Op

instance : Inhabited Op := ⟨null ()⟩

@[extern "op_getKind"]
opaque getKind : Op → Kind

@[extern "op_isNull"]
opaque isNull : Op → Bool

@[extern "op_isIndexed"]
opaque isIndexed : Op → Bool

@[extern "op_getNumIndices"]
opaque getNumIndices : Op → Nat

@[extern "op_get"]
protected opaque get : (op : Op) → Fin op.getNumIndices → Term

instance : GetElem Op Nat Term fun op i => i < op.getNumIndices where
  getElem op i h := op.get ⟨i, h⟩

@[extern "op_toString"]
protected opaque toString : Op → String

instance : ToString Op := ⟨Op.toString⟩

end Op

namespace Term

@[extern "term_null"]
opaque null : Unit → Term

instance : Inhabited Term := ⟨null ()⟩

@[extern "term_isNull"]
opaque isNull : Term → Bool

@[extern "term_getKind"]
opaque getKind : Term → Kind

@[extern "term_getOp"]
opaque getOp : Term → Op

@[extern "term_getSort"]
opaque getSort : Term → cvc5.Sort

@[extern "term_beq"]
protected opaque beq : Term → Term → Bool

instance : BEq Term := ⟨Term.beq⟩

@[extern "term_hash"]
protected opaque hash : Term → UInt64

instance : Hashable Term := ⟨Term.hash⟩

@[extern "term_getBooleanValue"]
opaque getBooleanValue : Term → Bool

@[extern "term_getBitVectorValue"]
opaque getBitVectorValue : Term → UInt32 → String

@[extern "term_getIntegerValue"]
opaque getIntegerValue : Term → Int

@[extern "term_getRationalValue"]
opaque getRationalValue : Term → Rat

@[extern "term_hasSymbol"]
opaque hasSymbol : Term → Bool

@[extern "term_getSymbol"]
opaque getSymbol : Term → String

@[extern "term_getId"]
opaque getId : Term → Nat

@[extern "term_getNumChildren"]
opaque getNumChildren : Term → Nat

@[extern "term_isSkolem"]
opaque isSkolem : Term → Bool

@[extern "term_getSkolemId"]
opaque getSkolemId : Term → SkolemFunId

@[extern "term_getSkolemIndices"]
opaque getSkolemIndices : Term → Array Term

@[extern "term_get"]
protected opaque get : (t : Term) → Fin t.getNumChildren → Term

instance : GetElem Term Nat Term fun t i => i < t.getNumChildren where
  getElem t i h := t.get ⟨i, h⟩

protected def forIn {β : Type u} [Monad m] (t : Term) (b : β) (f : Term → β → m (ForInStep β)) : m β :=
  let rec loop (i : Nat) (h : i ≤ t.getNumChildren) (b : β) : m β := do
    match i, h with
    | 0,   _ => pure b
    | i+1, h =>
      have h' : i < t.getNumChildren := Nat.lt_of_lt_of_le (Nat.lt_succ_self i) h
      have : t.getNumChildren - 1 < t.getNumChildren := Nat.sub_lt (Nat.zero_lt_of_lt h') (by decide)
      have : t.getNumChildren - 1 - i < t.getNumChildren := Nat.lt_of_le_of_lt (Nat.sub_le (t.getNumChildren - 1) i) this
      match (← f t[t.getNumChildren - 1 - i] b) with
      | ForInStep.done b  => pure b
      | ForInStep.yield b => loop i (Nat.le_of_lt h') b
  loop t.getNumChildren (Nat.le_refl _) b

instance : ForIn m Term Term where
  forIn := Term.forIn

@[extern "term_not"]
protected opaque not : Term → Term

@[extern "term_and"]
protected opaque and : Term → Term → Term

@[extern "term_or"]
protected opaque or : Term → Term → Term

@[extern "term_toString"]
protected opaque toString : Term → String

instance : ToString Term := ⟨Term.toString⟩

end Term

namespace Proof

@[extern "proof_null"]
opaque null : Unit → Proof

instance : Inhabited Proof := ⟨null ()⟩

@[extern "proof_getRule"]
opaque getRule : Proof → ProofRule

@[extern "proof_getResult"]
opaque getResult : Proof → Term

@[extern "proof_getChildren"]
opaque getChildren : Proof → Array Proof

@[extern "proof_getArguments"]
opaque getArguments : Proof → Array Term

@[extern "proof_beq"]
protected opaque beq : Proof → Proof → Bool

instance : BEq Proof := ⟨Proof.beq⟩

@[extern "proof_hash"]
protected opaque hash : Proof → UInt64

instance : Hashable Proof := ⟨Proof.hash⟩

end Proof

namespace TermManager

@[extern "termManager_new"]
opaque new : BaseIO TermManager

@[extern "termManager_mkBoolean"]
opaque mkBoolean : TermManager → Bool → Term

@[extern "termManager_mkIntegerFromString"]
private opaque mkIntegerFromString : TermManager → String → Term

def mkInteger (tm : TermManager) : Int → Term :=
  (mkIntegerFromString tm) ∘ toString

@[extern "termManager_mkTerm"]
opaque mkTerm : TermManager → Kind → (children : Array Term := #[]) → Term

end TermManager

namespace Solver

variable [Monad m]

@[export solver_val]
private def val (a : α) : SolverT m α := pure a

@[export solver_err]
private def err (e : Error) : SolverT m α := throw e

@[extern "solver_new"]
private opaque new : TermManager → Solver

@[extern "solver_getVersion"]
opaque getVersion : SolverT m String

@[extern "solver_setOption"]
opaque setOption (option value : String) : SolverT m Unit

@[extern "solver_assertFormula"]
opaque assertFormula : Term → SolverT m Unit

@[extern "solver_checkSat"]
opaque checkSat : SolverT m Result

@[extern "solver_getProof"]
opaque getProof : SolverT m (Array Proof)

@[extern "solver_proofToString"]
opaque proofToString : Proof → SolverT m String

@[extern "solver_parse"]
opaque parse : String → SolverT m Unit

def run (tm : TermManager) (query : SolverT m α) : m (Except Error α) :=
  return match ← ExceptT.run query (new tm) with
  | (.ok x, _) => .ok x
  | (.error e, _) => .error e

end Solver

end cvc5
