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

/-- Encapsulation of a three-valued solver result, with explanations. -/
def Result : Type := ResultImpl.type

instance Result.instNonemptyResult : Nonempty Result := ResultImpl.property

private opaque SortImpl : NonemptyType.{0}

end cvc5

/-- The sort of a cvc5 term. -/
def cvc5.Sort : Type := cvc5.SortImpl.type

namespace cvc5

instance Sort.instNonemptySort : Nonempty cvc5.Sort := SortImpl.property

private opaque OpImpl : NonemptyType.{0}

/-- A cvc5 operator.

An operator is a term that represents certain operators, instantiated with its required parameters,
*e.g.*, a `Term` of kind `Kind.BITVECTOR_EXTRACT`.
-/
def Op : Type := OpImpl.type

instance Op.instNonemptyOp : Nonempty Op := OpImpl.property

private opaque TermImpl : NonemptyType.{0}

/-- A cvc5 term. -/
def Term : Type := TermImpl.type

instance Term.instNonemptyTerm : Nonempty Term := TermImpl.property

private opaque ProofImpl : NonemptyType.{0}

/-- A cvc5 proof.

Proofs are trees and every proof object corresponds to the root step of a proof. The branches of the
root step are the premises of the step.
-/
def Proof : Type := ProofImpl.type

instance Proof.instNonemptyProof : Nonempty Proof := ProofImpl.property

private opaque TermManagerImpl : NonemptyType.{0}

/-- Manager for cvc5 terms. -/
def TermManager : Type := TermManagerImpl.type

instance TermManager.instNonemptyTermManager : Nonempty TermManager := TermManagerImpl.property

/-- Error type. -/
inductive Error where
  | missingValue
  | userError (msg : String)
  | cvc5Error (msg : String)
deriving Repr

/-- Only used by FFI to inject values. -/
@[export except_ok]
private def mkExceptOk {α : Type} : α → Except Error α :=
  .ok

/-- Only used by FFI to inject values. -/
@[export except_ok_bool]
private def mkExceptOkBool : Bool → Except Error Bool :=
  .ok

/-- Only used by FFI to inject errors. -/
@[export except_err]
private def mkExceptErr {α : Type} : String → Except Error α :=
  .error ∘ Error.cvc5Error

private opaque SolverImpl : NonemptyType.{0}

/-- A cvc5 solver. -/
def Solver : Type := SolverImpl.type

instance Solver.instNonemptySolver : Nonempty Solver := SolverImpl.property

/-- Solver error/state-monad transformer. -/
abbrev SolverT m := ExceptT Error (StateT Solver m)

/-- Solver error/state-monad wrapped in `IO`. -/
abbrev SolverM := SolverT IO

namespace Error

/-- Panics on errors, otherwise yields the `ok` result. -/
def unwrap! [Inhabited α] : Except Error α → α
| .ok a => a
| .error (.userError e) => panic! s!"user error: {e}"
| .error (.cvc5Error e) => panic! s!"cvc5 error: {e}"
| .error .missingValue => panic! s!"missing value"

/-- String representation of an error. -/
protected def toString : Error → String :=
  toString ∘ repr

instance : ToString Error :=
  ⟨Error.toString⟩

end Error

namespace Result

/-- True if this result is from a satisfiable `checkSat` or `checkSatAssuming` query. -/
@[extern "result_isSat"]
opaque isSat : Result → Bool

/-- True if this result is from a unsatisfiable `checkSat` or `checkSatAssuming` query. -/
@[extern "result_isUnsat"]
opaque isUnsat : Result → Bool

/-- True if this result is from a `checkSat` or `checkSatAssuming` query and cvc5 was not able to
determine (un)satisfiability.
-/
@[extern "result_isUnknown"]
opaque isUnknown : Result → Bool

/-- A string representation of this result. -/
@[extern "result_toString"]
protected opaque toString : Result → String

instance : ToString Result := ⟨Result.toString⟩

end cvc5.Result

namespace cvc5.Sort

@[extern "sort_null"]
opaque null : Unit → cvc5.Sort

instance : Inhabited cvc5.Sort := ⟨null ()⟩

/-- Get the kind of this sort. -/
@[extern "sort_getKind"]
opaque getKind : cvc5.Sort → SortKind

/-- Comparison for structural equality. -/
@[extern "sort_beq"]
protected opaque beq : cvc5.Sort → cvc5.Sort → Bool

instance : BEq cvc5.Sort := ⟨Sort.beq⟩

/-- Hash function for cvc5 sorts. -/
@[extern "sort_hash"]
protected opaque hash : cvc5.Sort → UInt64

instance : Hashable cvc5.Sort := ⟨Sort.hash⟩

/-- Determine if this is a function sort. -/
@[extern "sort_isFunction"]
protected opaque isFunction : cvc5.Sort → Bool

/-- The domain sorts of a function sort. -/
@[extern "sort_getFunctionDomainSorts"]
opaque getFunctionDomainSorts : cvc5.Sort → Except Error (Array cvc5.Sort)

/-- The codomain sort of a function sort. -/
@[extern "sort_getFunctionCodomainSort"]
opaque getFunctionCodomainSort : cvc5.Sort → Except Error cvc5.Sort

/-- Get the symbol of this sort.

The symbol of this sort is the string that was provided when consrtucting it *via* one of
`Solver.mkUninterpretedSort`, `Solver.mkUnresolvedSort`, or
`Solver.mkUninterpretedSortConstructorSort`.
-/
@[extern "sort_getSymbol"]
opaque getSymbol : cvc5.Sort → Except Error String

/-- Determine if this is the integer sort (SMT-LIB: `Int`). -/
@[extern "sort_isInteger"]
opaque isInteger : cvc5.Sort → Bool

/-- The bit-width of the bit-vector sort. -/
@[extern "sort_getBitVectorSize"]
opaque getBitVectorSize : cvc5.Sort → Except Error UInt32

/-- A string representation of this sort. -/
@[extern "sort_toString"]
protected opaque toString : cvc5.Sort → String

instance : ToString cvc5.Sort := ⟨Sort.toString⟩
instance : Repr cvc5.Sort := ⟨fun self _ => self.toString⟩

end cvc5.Sort

namespace cvc5.Op

@[extern "op_null"]
opaque null : Unit → Op

instance : Inhabited Op := ⟨null ()⟩

/-- Syntactic equality operator. -/
@[extern "op_beq"]
protected opaque beq : Op → Op → Bool

instance : BEq Op := ⟨Op.beq⟩

/-- Get the kind of this operator. -/
@[extern "op_getKind"]
opaque getKind : Op → Kind

/-- Determine if this operator is nullary. -/
@[extern "op_isNull"]
opaque isNull : Op → Bool

/-- Determine if this operator is indexed. -/
@[extern "op_isIndexed"]
opaque isIndexed : Op → Bool

/-- Get the number of indices of this operator. -/
@[extern "op_getNumIndices"]
opaque getNumIndices : Op → Nat

/-- Get the index at position `i` of an indexed operator. -/
@[extern "op_get"]
protected opaque get : (op : Op) → (i : Fin op.getNumIndices) → Term

instance : GetElem Op Nat Term fun op i => i < op.getNumIndices where
  getElem op i h := op.get ⟨i, h⟩

/-- Get the string representation of this operator. -/
@[extern "op_toString"]
protected opaque toString : Op → String

instance : ToString Op := ⟨Op.toString⟩

end Op

namespace Term

@[extern "term_null"]
opaque null : Unit → Term

instance : Inhabited Term := ⟨null ()⟩

/-- Determine if this term is nullary. -/
@[extern "term_isNull"]
opaque isNull : Term → Bool

/-- Get the kind of this term. -/
@[extern "term_getKind"]
opaque getKind : Term → Kind

/-- Get the operator of a term with an operator. -/
@[extern "term_hasOp"]
opaque hasOp : Term → Bool

/-- Get the operator of a term with an operator.

Requires that this term has an operator (see `hasOp`).
-/
@[extern "term_getOp"]
private opaque getOp! : Term → Op

@[inherit_doc getOp!]
def getOp (term : Term) (_valid : term.hasOp) : Op :=
  term.getOp!

/-- Get the operator of a term, if any. -/
def getOp? (term : Term) : Option Op :=
  if valid : term.hasOp then
    term.getOp valid
  else
    none

/-- Get the sort of this term. -/
@[extern "term_getSort"]
opaque getSort : Term → cvc5.Sort

/-- Syntactic equality operator. -/
@[extern "term_beq"]
protected opaque beq : Term → Term → Bool

instance : BEq Term := ⟨Term.beq⟩

/-- Hash function for terms. -/
@[extern "term_hash"]
protected opaque hash : Term → UInt64

instance : Hashable Term := ⟨Term.hash⟩

/-- Get the value of a Boolean term as a native Boolean value.

Requires `term` to have sort Bool.
-/
@[extern "term_getBooleanValue"]
opaque getBooleanValue : (term : Term) → Except Error Bool

/-- Get the string representation of a bit-vector value.

Requires `term` to have a bit-vector sort.

- `base`: `2` for binary, `10` for decimal, and `16` for hexadecimal.
-/
@[extern "term_getBitVectorValue"]
opaque getBitVectorValue : Term → (base : UInt32 := 2) → Except Error String

/-- Get the native integral value of an integral value. -/
@[extern "term_getIntegerValue"]
opaque getIntegerValue : Term → Except Error Int

/-- Get the native rational value of a real, rational-compatible value. -/
@[extern "term_getRationalValue"]
opaque getRationalValue : Term → Except Error Lean.Rat

/-- Determine if this term has a symbol (a name).

For example, free constants and variables have symbols.
-/
@[extern "term_hasSymbol"]
opaque hasSymbol : Term → Bool

/-- Get the symbol of this term.

Requires that this term has a symbol (see `hasSymbol`).

The symbol of the term is the string that was provided when constructing it *via*
`TermManager.mkConst` or `TermManager.mkVar`.
-/
@[extern "term_getSymbol"]
private opaque getSymbol! : Term → String

@[inherit_doc getSymbol!]
def getSymbol (term : Term) (_valid : term.hasSymbol) : String :=
  term.getSymbol!

/-- Get the symbol of this term, if any. -/
def getSymbol? (term : Term) : Option String :=
  if valid : term.hasSymbol then
    term.getSymbol valid
  else
    none

/-- Get the id of this term. -/
@[extern "term_getId"]
opaque getId : Term → Nat

/-- Get the number of children of this term. -/
@[extern "term_getNumChildren"]
opaque getNumChildren : Term → Nat

/-- Is this term a skolem? -/
@[extern "term_isSkolem"]
opaque isSkolem : Term → Bool

/-- Get skolem identifier of this term.

Requires `isSkolem`.
-/
@[extern "term_getSkolemId"]
opaque getSkolemId! : Term → SkolemId

@[inherit_doc getSkolemId!]
def getSkolemId (term : Term) (_valid : term.isSkolem) : SkolemId :=
  term.getSkolemId!

/-- Get skolem identifier of this term, if any. -/
def getSkolemId? (term : Term) : Option SkolemId :=
  if valid : term.isSkolem then
    term.getSkolemId valid
  else
    none

/-- Get the skolem indices of this term.

Requires `isSkolem`.

Returns the skolem indices of this term. This is a list of terms that the skolem function is indexed
by. For example, the array diff skolem `SkolemId.ARRAY_DEQ_DIFF` is indexed by two arrays.
-/
@[extern "term_getSkolemIndices"]
private opaque getSkolemIndices! : Term → Array Term

@[inherit_doc getSkolemIndices!]
def getSkolemIndices (term : Term) (_valid : term.isSkolem) : Array Term :=
  term.getSkolemIndices!

/-- Get the skolem indices of this term, if any.

Returns the skolem indices of this term. This is a list of terms that the skolem function is indexed
by. For example, the array diff skolem `SkolemId.ARRAY_DEQ_DIFF` is indexed by two arrays.
-/
def getSkolemIndices? (term : Term) : Option (Array Term) :=
  if valid : term.isSkolem then
    term.getSkolemIndices valid
  else
    none

/-- Get the child term of this term at a given index. -/
@[extern "term_get"]
protected opaque get : (t : Term) → Fin t.getNumChildren → Term

instance : GetElem Term Nat Term fun t i => i < t.getNumChildren where
  getElem t i h := t.get ⟨i, h⟩

/-- Monadic for-loop as required by `ForIn`. -/
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

/-- Get the children of a term. -/
def getChildren (t : Term) : Array Term := Id.run do
  let mut cts := #[]
  for ct in t do
    cts := cts.push ct
  cts

/-- Boolean negation. -/
@[extern "term_not"]
protected opaque not : Term → Term

/-- Boolean and. -/
@[extern "term_and"]
protected opaque and : Term → Term → Term

/-- Boolean or. -/
@[extern "term_or"]
protected opaque or : Term → Term → Term

/-- A string representation of this term. -/
@[extern "term_toString"]
protected opaque toString : Term → String

instance : ToString Term := ⟨Term.toString⟩

end Term

namespace Proof

@[extern "proof_null"]
opaque null : Unit → Proof

instance : Inhabited Proof := ⟨null ()⟩

/-- The proof rule used by the root step of the proof. -/
@[extern "proof_getRule"]
opaque getRule : Proof → ProofRule

/-- The proof rewrite rule used by the root step of the proof. -/
@[extern "proof_getRewriteRule"]
opaque getRewriteRule : Proof → ProofRewriteRule

/-- The conclusion of the root step of the proof. -/
@[extern "proof_getResult"]
opaque getResult : Proof → Term

/-- The premises of the root step of the proof. -/
@[extern "proof_getChildren"]
opaque getChildren : Proof → Array Proof

/-- The arguments of the root step of the proof as a vector of terms.

Some of those terms might be strings.
-/
@[extern "proof_getArguments"]
opaque getArguments : Proof → Array Term

/-- Operator overloading for referential equality of two proofs. -/
@[extern "proof_beq"]
protected opaque beq : Proof → Proof → Bool

instance : BEq Proof := ⟨Proof.beq⟩

/-- Hash function for proofs. -/
@[extern "proof_hash"]
protected opaque hash : Proof → UInt64

instance : Hashable Proof := ⟨Proof.hash⟩

end Proof

namespace TermManager

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

- `indexSort`: The array index sort.
- `elemSort`: The array element sort.
-/
@[extern "termManager_mkArraySort"]
opaque mkArraySort : TermManager → (indexSort elemSort : cvc5.Sort) → Except Error cvc5.Sort

@[inherit_doc mkArraySort]
def mkArraySort! tm indexSort elemSort :=
  mkArraySort tm indexSort elemSort
  |> Error.unwrap!

/-- Create a bit-vector sort.

- `size`: The bit-width of the bit-vector sort.
-/
@[extern "termManager_mkBitVectorSort"]
private opaque mkBitVectorSortUnsafe : TermManager → (size : UInt32) → Except Error cvc5.Sort

@[inherit_doc mkBitVectorSortUnsafe]
def mkBitVectorSort (tm : TermManager) (size : UInt32) (_valid : 0 < size := by simp) : cvc5.Sort :=
  tm.mkBitVectorSortUnsafe size
  |> Error.unwrap!

/-- Create a floating-point sort.

- `exp`: The bit-width of the exponent of the floating-point sort.
- `sig`: The bit-width of the significand of the floating-point sort.
-/
@[extern "termManager_mkFloatingPointSort"]
private opaque mkFloatingPointSortUnsafe : TermManager → (exp sig : UInt32) → Except Error cvc5.Sort

@[inherit_doc mkFloatingPointSortUnsafe]
def mkFloatingPointSort
  (tm : TermManager) (exp sig : UInt32)
  (_valid_exp : 1 < exp := by simp) (_valid_sig : 1 < sig := by simp)
: Except Error cvc5.Sort :=
  tm.mkFloatingPointSortUnsafe exp sig

@[inherit_doc mkFloatingPointSort]
def mkFloatingPointSort! tm (exp sig : UInt32)
  (valid_exp : 1 < exp := by simp) (valid_sig : 1 < sig := by simp)
:=
  mkFloatingPointSort tm exp sig valid_exp valid_sig
  |> Error.unwrap!

/-- Create a finite-field sort from a given string of base n.

- `size`: The modulus of the field. Must be prime.
- `base`: The base of the string representation of `size`.
-/
@[extern "termManager_mkFiniteFieldSort"]
opaque mkFiniteFieldSortOfString
: TermManager → (size : String) → (base : UInt32 := 10) → Except Error cvc5.Sort

@[inherit_doc mkFiniteFieldSortOfString]
def mkFiniteFieldSortOfString! tm size (base : UInt32 := 10) :=
  mkFiniteFieldSortOfString tm size base
  |> Error.unwrap!

/-- Create a finite-field sort from a given string of base n.

- `size`: The modulus of the field. Must be prime.
- `base`: The base of `size`.
-/
def mkFiniteFieldSort
  (tm : TermManager) (size : Nat) (base : UInt32 := 10)
: Except Error cvc5.Sort :=
  tm.mkFiniteFieldSortOfString (toString size) base

@[inherit_doc mkFiniteFieldSort]
def mkFiniteFieldSort! tm size base :=
  mkFiniteFieldSort tm size base
  |> Error.unwrap!

/-- Create function sort.

- `sorts`: The sort of the function arguments.
- `codomain`: The sort of the function return value.
-/
@[extern "termManager_mkFunctionSort"]
opaque mkFunctionSort
: TermManager → (sorts : Array cvc5.Sort) → (codomain : cvc5.Sort) → Except Error cvc5.Sort

@[inherit_doc mkFunctionSort]
def mkFunctionSort! tm sorts codomain :=
  mkFunctionSort tm sorts codomain
  |> Error.unwrap!

/-- Create a Boolean constant.

- `b`: The Boolean constant.
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

- `i`: The integer constant.
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

- `kind`: The kind of the operator.
- `args`: The arguments (indices) of the operator.

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

- `kind`: The kind of the operator.
- `arg`: The string argument to this operator.

-/
@[extern "termManager_mkOpOfString"]
private opaque mkOpOfString : TermManager → (kind : Kind) → (arg : String) → Except Error Op

/-- Create divisibility-by operator, supports arbitrary precision. -/
def mkOpDivisible (tm : TermManager) (n : Nat) (_valid : 0 < n := by simp) : Op :=
  tm.mkOpOfString Kind.DIVISIBLE (toString n)
  |> Error.unwrap!

/-- Create n-ary term of given kind.

- `kind`: The kind of the term.
- `children`: The children of the term.
-/
@[extern "termManager_mkTerm"]
opaque mkTerm : TermManager → (kind : Kind) → (children : Array Term := #[]) → Except Error Term

@[inherit_doc mkTerm]
def mkTerm! tm kind children :=
  mkTerm tm kind children
  |> Error.unwrap!

/-- Create n-ary term of given kind from a given operator.

Create operators with `mkOp`.

- `op`: The operator.
- `children`: The children of the term.
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

- `sort`: The sort of the constant.
- `symbol`: The name of the constant.
-/
@[extern "termManager_mkConst"]
opaque mkConst : TermManager → (sort : cvc5.Sort) → (symbol : String) → Term

end TermManager

namespace Solver

variable [Monad m]

/-- Only used by FFI to wrap *success* results. -/
@[export solver_val]
private def val (a : α) : SolverT m α := pure a

/-- Only used by FFI to wrap errors. -/
@[export solver_err]
private def err (e : Error) : SolverT m α := throw e

/-- Only used by FFI to wrap cvc5 errors. -/
@[export solver_errOfString]
private def cvc5ErrOfString (msg : String) : SolverT m α := throw (.cvc5Error msg)

/-- Constructor.

Constructs solver instance from a given term manager instance.

- `tm`: The associated term manager.
-/
@[extern "solver_new"]
private opaque new : (tm : TermManager) → Solver

/-- Get a string representation of the version of this solver. -/
@[extern "solver_getVersion"]
opaque getVersion : SolverT m String

/-- Set option.

- `option`: The option name.
- `value`: The option value.
-/
@[extern "solver_setOption"]
opaque setOption (option value : String) : SolverT m Unit

/-- Set logic.

- `logic`: The logic to set.
-/
@[extern "solver_setLogic"]
opaque setLogic (logic : String) : SolverT m Unit

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

/-- Declares a sort symbol `symbol` with arity `arity`.

If `fresh`, then a new (fresh) `Sort` is always produced; otherwise, the `Sort` will always be
(physically) the same.

See also `declareFreshSort`.
-/
@[extern "solver_declareSort"]
opaque declareSort :
  (symbol : String) → (arity: Nat) → (fresh : Bool) → SolverT m cvc5.Sort

/-- Assert a formula.

- `term`: The formula to assert.
-/
@[extern "solver_assertFormula"]
opaque assertFormula : (term : Term) → SolverT m Unit

/-- Check satisfiability. -/
@[extern "solver_checkSat"]
opaque checkSat : SolverT m Result

/-- Get a proof associated with the most recent call to `checkSat`.

Requires to enable option `produce-proofs`
-/
@[extern "solver_getProof"]
opaque getProof : SolverT m (Array Proof)

/-- Get the value of the given term in the current model.

- `term`: The term for which the value is queried.
-/
@[extern "solver_getValue"]
opaque getValue : (term : Term) → SolverT m Term

/-- Get the values of the given terms in the current model.

- `term`: The terms for which the value is queried.
-/
@[extern "solver_getValues"]
opaque getValues : (term : Array Term) → SolverT m (Array Term)

/-- Prints a proof as a string in a selected proof format mode.

Other aspects of printing are taken from the solver options.

- `proof`: A proof, usually obtained from `getProof`.
-/
@[extern "solver_proofToString"]
opaque proofToString : (proof : Proof) → SolverT m String

/-- Parse a string containing SMT-LIB commands.

Commands that produce a result such as `(check-sat)`, `(get-model)`, ... are executed but the
results are ignored.
-/
@[extern "solver_parse"]
opaque parse : String → SolverT m Unit

/-- Run a `query` given a term manager `tm`. -/
def run (tm : TermManager) (query : SolverT m α) : m (Except Error α) :=
  return match ← ExceptT.run query (new tm) with
  | (.ok x, _) => .ok x
  | (.error e, _) => .error e

end Solver

end cvc5
