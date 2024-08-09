/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Lean.Data.Rat

import cvc5.Kind
import cvc5.ProofRule
import cvc5.SkolemId

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
  | userError (msg : String)
  | cvc5Error (msg : String)
deriving Repr

private opaque SolverImpl : NonemptyType.{0}

def Solver : Type := SolverImpl.type

instance Solver.instNonemptySolver : Nonempty Solver := SolverImpl.property

abbrev SolverT m := ExceptT Error (StateT Solver m)

abbrev SolverM := SolverT IO

namespace Error

def unwrap! [Inhabited α] : Except Error α → α
| .ok a => a
| .error (.userError e) => panic! s!"user error: {e}"
| .error (.cvc5Error e) => panic! s!"cvc5 error: {e}"
| .error .missingValue => panic! s!"missing value"

protected def toString : Error → String :=
  toString ∘ repr

instance : ToString Error :=
  ⟨Error.toString⟩

end Error

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

end cvc5.Result

namespace cvc5.Sort

@[extern "sort_null"]
opaque null : Unit → cvc5.Sort

instance : Inhabited cvc5.Sort := ⟨null ()⟩

@[extern "sort_getKind"]
opaque getKind : cvc5.Sort → SortKind

@[extern "sort_beq"]
protected opaque beq : cvc5.Sort → cvc5.Sort → Bool

instance : BEq cvc5.Sort := ⟨Sort.beq⟩

@[extern "sort_hash"]
protected opaque hash : cvc5.Sort → UInt64

instance : Hashable cvc5.Sort := ⟨Sort.hash⟩

@[extern "sort_getFunctionDomainSorts"]
opaque getFunctionDomainSorts : cvc5.Sort → Array cvc5.Sort

@[extern "sort_getFunctionCodomainSort"]
opaque getFunctionCodomainSort : cvc5.Sort → cvc5.Sort

@[extern "sort_getSymbol"]
opaque getSymbol : cvc5.Sort → String

@[extern "sort_isInteger"]
opaque isInteger : cvc5.Sort → Bool

@[extern "sort_getBitVectorSize"]
opaque getBitVectorSize : cvc5.Sort → UInt32

@[extern "sort_toString"]
protected opaque toString : cvc5.Sort → String

instance : ToString cvc5.Sort := ⟨Sort.toString⟩
instance : Repr cvc5.Sort := ⟨fun self _ => self.toString⟩

end cvc5.Sort

namespace cvc5.Op

@[extern "op_null"]
opaque null : Unit → Op

instance : Inhabited Op := ⟨null ()⟩

@[extern "op_beq"]
protected opaque beq : Op → Op → Bool

instance : BEq Op := ⟨Op.beq⟩

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
opaque getRationalValue : Term → Lean.Rat

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
opaque getSkolemId : Term → SkolemId

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

def getChildren (t : Term) : Array Term := Id.run do
  let mut cts := #[]
  for ct in t do
    cts := cts.push ct
  cts

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

@[extern "proof_getRewriteRule"]
opaque getRewriteRule : Proof → ProofRewriteRule

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

/-- Only used by FFI to inject values. -/
@[export termManager_val]
private def val {α : Type} : α → Except Error α :=
  .ok

/-- Only used by FFI to inject errors. -/
@[export termManager_err]
private def err {α : Type} : String → Except Error α :=
  .error ∘ Error.cvc5Error

@[extern "termManager_new"]
opaque new : BaseIO TermManager

/-- Get the Boolean sort. -/
@[extern "termManager_getBooleanSort"]
opaque getBooleanSort : TermManager → cvc5.Sort

/-- Get the Integer sort. -/
@[extern "termManager_getIntegerSort"]
opaque getIntegerSort : TermManager → cvc5.Sort

/-- Get the Real sort. -/
@[extern "termManager_getRealSort"]
opaque getRealSort : TermManager → cvc5.Sort

/-- Get the regular expression sort. -/
@[extern "termManager_getRegExpSort"]
opaque getRegExpSort : TermManager → cvc5.Sort

/-- Get the rounding mode sort. -/
@[extern "termManager_getRoundingModeSort"]
opaque getRoundingModeSort : TermManager → cvc5.Sort

/-- Get the string sort. -/
@[extern "termManager_getStringSort"]
opaque getStringSort : TermManager → cvc5.Sort

/-- Create an array sort.

- `indexSort` The array index sort.
- `elemSort` The array element sort.
-/
@[extern "termManager_mkArraySort"]
opaque mkArraySort : TermManager → (indexSort elemSort : cvc5.Sort) → Except Error cvc5.Sort

@[inherit_doc mkArraySort]
def mkArraySort! tm indexSort elemSort :=
  mkArraySort tm indexSort elemSort
  |> Error.unwrap!

/-- Create a bit-vector sort.

- `size` The bit-width of the bit-vector sort.
-/
@[extern "termManager_mkBitVectorSort"]
private opaque mkBitVectorSortUnsafe : TermManager → (size : UInt32) → Except Error cvc5.Sort

@[inherit_doc mkBitVectorSortUnsafe]
def mkBitVectorSort (tm : TermManager) (size : UInt32) (_valid : 0 < size := by simp) : cvc5.Sort :=
  tm.mkBitVectorSortUnsafe size
  |> Error.unwrap!

/-- Create a floating-point sort.

- `exp` The bit-width of the exponent of the floating-point sort.
- `sig` The bit-width of the significand of the floating-point sort.
-/
@[extern "termManager_mkFloatingPointSort"]
opaque mkFloatingPointSort : TermManager → (exp sig : UInt32) → Except Error cvc5.Sort

@[inherit_doc mkFloatingPointSort]
def mkFloatingPointSort! tm exp sig :=
  mkFloatingPointSort tm exp sig
  |> Error.unwrap!

/-- Create a finite-field sort from a given string of base n.

- `size` The modulus of the field. Must be prime.
- `base` The base of the string representation of `size`.
-/
@[extern "termManager_mkFiniteFieldSort"]
opaque mkFiniteFieldSortOfString
: TermManager → (size : String) → (base : UInt32) → Except Error cvc5.Sort

/-- Create a finite-field sort from a given string of base n.

- `size` The modulus of the field. Must be prime.
- `base` The base of `size`.
-/
def mkFiniteFieldSort
  (tm : TermManager) (size : Nat) (base : UInt32 := 10)
: Except Error cvc5.Sort :=
  tm.mkFiniteFieldSortOfString (toString size) base

@[inherit_doc mkFiniteFieldSort]
def mkFiniteFieldSort! tm size base :=
  mkFloatingPointSort tm size base
  |> Error.unwrap!

/-- Create function sort.

- `sorts` The sort of the function arguments.
- `codomain` The sort of the function return value.
-/
@[extern "termManager_mkFunctionSort"]
opaque mkFunctionSort
: TermManager → (sorts : Array cvc5.Sort) → (codomain : cvc5.Sort) → Except Error cvc5.Sort

@[inherit_doc mkFunctionSort]
def mkFunctionSort! tm sorts codomain :=
  mkFunctionSort tm sorts codomain
  |> Error.unwrap!

/-- Create a Boolean constant.

- `b` The Boolean constant.
-/
@[extern "termManager_mkBoolean"]
opaque mkBoolean : TermManager → (b : Bool) → Except Error Term

@[inherit_doc mkBoolean]
def mkBoolean! tm b :=
  mkBoolean tm b
  |> Error.unwrap!

@[extern "termManager_mkIntegerFromString"]
private opaque mkIntegerFromString : TermManager → String → Except Error Term

/-- Create an integer constant.

- `i` The integer constant.
-/
def mkInteger (tm : TermManager) : (i : Int) → Except Error Term :=
  mkIntegerFromString tm ∘ toString

@[inherit_doc mkInteger]
def mkInteger! tm i :=
  mkInteger tm i
  |> Error.unwrap!

/-- Create operator of Kind:

- `Kind.BITVECTOR_EXTRACT`
- `Kind.BITVECTOR_REPEAT`
- `Kind.BITVECTOR_ROTATE_LEFT`
- `Kind.BITVECTOR_ROTATE_RIGHT`
- `Kind.BITVECTOR_SIGN_EXTEND`
- `Kind.BITVECTOR_ZERO_EXTEND`
- `Kind.DIVISIBLE`
- `Kind.FLOATINGPOINT_TO_FP_FROM_FP`
- `Kind.FLOATINGPOINT_TO_FP_FROM_IEEE_BV`
- `Kind.FLOATINGPOINT_TO_FP_FROM_REAL`
- `Kind.FLOATINGPOINT_TO_FP_FROM_SBV`
- `Kind.FLOATINGPOINT_TO_FP_FROM_UBV`
- `Kind.FLOATINGPOINT_TO_SBV`
- `Kind.FLOATINGPOINT_TO_UBV`
- `Kind.INT_TO_BITVECTOR`
- `Kind.TUPLE_PROJECT`

See `cvc5.Kind` for a description of the parameters.

- `kind` The kind of the operator.
- `args` The arguments (indices) of the operator.

If `args` is empty, the `Op` simply wraps the `cvc5.Kind`. The `Kind` can be used in `Solver.mkTerm`
directly without creating an `Op` first.
-/
@[extern "termManager_mkOpOfIndices"]
opaque mkOpOfIndices : TermManager → (kind : Kind) → (args : Array Nat) → Except Error Op

@[inherit_doc mkOpOfIndices]
def mkOpOfIndices! tm kind args :=
  mkOpOfIndices tm kind args
  |> Error.unwrap!

/-- Create operator of kind:

- `Kind.DIVISIBLE` (to support arbitrary precision integers)

See `cvc5.Kind` for a description of the parameters.

- `kind` The kind of the operator.
- `arg` The string argument to this operator.

-/
@[extern "termManager_mkOpOfString"]
private opaque mkOpOfString : TermManager → (kind : Kind) → (arg : String) → Except Error Op

/-- Create divisibility-by operator, supports arbitrary precision. -/
def mkOpDivisible (tm : TermManager) (n : Nat) (_valid : 0 < n := by simp) : Op :=
  tm.mkOpOfString Kind.DIVISIBLE (toString n)
  |> Error.unwrap!

/-- Create n-ary term of given kind.

- `kind` The kind of the term.
- `children` The children of the term.
-/
@[extern "termManager_mkTerm"]
opaque mkTerm : TermManager → (kind : Kind) → (children : Array Term := #[]) → Except Error Term

@[inherit_doc mkTerm]
def mkTerm! tm kind children :=
  mkTerm tm kind children
  |> Error.unwrap!

/-- Create n-ary term of given kind from a given operator.

Create operators with `mkOp`.

- `op` The operator.
- `children` The children of the term.
-/
@[extern "termManager_mkTermOfOp"]
opaque mkTermOfOp : TermManager → (op : Op) → (children : Array Term := #[]) → Except Error Term

@[inherit_doc mkTermOfOp]
def mkTermOfOp! tm op children :=
  mkTermOfOp tm op children
  |> Error.unwrap!

/-- Create a free constant.

Note that the returned term is always fresh, even if the same arguments were provided on a previous
call to `mkConst`.

- `sort` The sort of the constant.
- `symbol` The name of the constant.
-/
@[extern "termManager_mkConst"]
opaque mkConst : TermManager → (sort : cvc5.Sort) → (symbol : String) → Term

end TermManager

namespace Solver

variable [Monad m]

@[export solver_val]
private def val (a : α) : SolverT m α := pure a

@[export solver_err]
private def err (e : Error) : SolverT m α := throw e

@[export solver_errOfString]
private def cvc5ErrOfString (msg : String) : SolverT m α := throw (.cvc5Error msg)

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
