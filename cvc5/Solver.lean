import Std.Data.Rat.Basic

import cvc5.Kind
import cvc5.ProofRule

@[export rat_mk]
private def Rat.mk : Int → Nat → Rat := mkRat

namespace cvc5

private opaque ResultImpl : NonemptyType.{0}

def Result : Type := ResultImpl.type

namespace Result

instance : Nonempty Result := ResultImpl.property

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

private opaque SortImpl : NonemptyType.{0}

end cvc5

def cvc5.Sort : Type := cvc5.SortImpl.type

namespace cvc5

instance : Nonempty cvc5.Sort := SortImpl.property

@[extern "sort_null"]
opaque Sort.null : Unit → cvc5.Sort

instance : Inhabited cvc5.Sort := ⟨Sort.null ()⟩

@[extern "sort_getKind"]
opaque Sort.getKind : cvc5.Sort → SortKind

@[extern "sort_isInteger"]
opaque Sort.isInteger : cvc5.Sort → Bool

@[extern "sort_getBitVectorSize"]
opaque Sort.getBitVectorSize : cvc5.Sort → UInt32

@[extern "sort_toString"]
protected opaque Sort.toString : cvc5.Sort → String

instance : ToString cvc5.Sort := ⟨Sort.toString⟩

private opaque TermImpl : NonemptyType.{0}

def Term : Type := TermImpl.type

namespace Term

instance : Nonempty Term := TermImpl.property

@[extern "term_null"]
opaque null : Unit → Term

instance : Inhabited Term := ⟨null ()⟩

@[extern "term_isNull"]
opaque isNull : Term → Bool

@[extern "term_getKind"]
opaque getKind : Term → Kind

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

@[extern "term_getNumChildren"]
opaque getNumChildren : Term → Nat

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

private opaque ProofImpl : NonemptyType.{0}

def Proof : Type := ProofImpl.type

namespace Proof

instance : Nonempty Proof := ProofImpl.property

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

private opaque SolverImpl : NonemptyType.{0}

def Solver : Type := SolverImpl.type

inductive SolverError where
  | missingValue
  | user_error (msg : String)
deriving Repr

abbrev SolverT m := ExceptT SolverError (StateT Solver m)

abbrev SolverM := SolverT IO

namespace Solver

variable [Monad m]

@[export solver_val]
private def val (a : α) : SolverT m α := pure a

@[export solver_err]
private def err (e : SolverError) : SolverT m α := throw e

instance : Nonempty Solver := SolverImpl.property

@[extern "solver_new"]
private opaque new : Unit → Solver

@[extern "solver_getVersion"]
opaque getVersion : SolverT m String

@[extern "solver_setOption"]
opaque setOption (option value : String) : SolverT m Unit

@[extern "solver_mkBoolean"]
opaque mkBoolean : Bool → SolverT m Term

/-- condition: `-2⁶³ ≤ x < 2⁶³` -/
@[extern "solver_mkInteger"]
opaque mkInteger : (x : Int) → SolverT m Term

@[extern "solver_mkTerm"]
opaque mkTerm (kind : Kind) (children : Array Term := #[]) : SolverT m Term

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

@[export solver_runp]
private def run' (query : SolverT m α) (s : Solver) : m (Except SolverError α) := do
  return match ← ExceptT.run query s with
  | (.ok x, _) => .ok x
  | (.error e, _) => .error e

@[extern "solver_run"]
opaque run (query : SolverT m α) : m (Except SolverError α) :=
  run' query (new ())

end Solver

end cvc5
