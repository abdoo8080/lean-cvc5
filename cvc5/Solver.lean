/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Lean.Data.Rat

import cvc5.Init
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
  | error (msg : String)
  | recoverable (msg : String)
  | unsupported (msg : String)
  | option (msg : String)
deriving Repr

private opaque SolverImpl : NonemptyType.{0}

/-- A cvc5 solver. -/
def Solver : Type := SolverImpl.type

instance Solver.instNonemptySolver : Nonempty Solver := SolverImpl.property

/-- Solver error/state-monad transformer. -/
abbrev SolverT m := ExceptT Error (StateT Solver m)

/-- Solver error/state-monad wrapped in `IO`. -/
abbrev SolverM := SolverT IO

namespace Error

/-- String representation of an error. -/
protected def toString : Error → String :=
  toString ∘ repr

/-- Panics on errors, otherwise yields the `ok` result. -/
def unwrap! [Inhabited α] : Except Error α → α
| .ok a => a
| .error e => panic! e.toString

instance : ToString Error :=
  ⟨Error.toString⟩

end Error

namespace Result

extern! "result"

  /-- True if this result is from a satisfiable `checkSat` or `checkSatAssuming` query. -/
  def isSat : Result → Bool

  /-- True if this result is from a unsatisfiable `checkSat` or `checkSatAssuming` query. -/
  def isUnsat : Result → Bool

  /-- True if this result is from a `checkSat` or `checkSatAssuming` query and cvc5 was not able to
  determine (un)satisfiability.
  -/
  def isUnknown : Result → Bool

  /-- A string representation of this result. -/
  protected def toString : Result → String

instance : ToString Result := ⟨Result.toString⟩

end Result

section ffi_except_constructors
/-- Only used by FFI to inject values. -/
@[export except_ok]
private def mkExceptOk {α : Type} : α → Except Error α :=
  .ok

/-- Only used by FFI to inject values. -/
@[export except_ok_bool]
private def mkExceptOkBool : Bool → Except Error Bool :=
  .ok

/-- Only used by FFI to inject values. -/
@[export except_ok_u32]
private def mkExceptOkU32 : UInt32 → Except Error UInt32 :=
  .ok

/-- Only used by FFI to inject values. -/
@[export except_ok_u8]
private def mkExceptOkU8 : UInt8 → Except Error UInt8 :=
  .ok

/-- Only used by FFI to inject errors. -/
@[export except_err]
private def mkExceptErr {α : Type} : String → Except Error α :=
  .error ∘ Error.error
end ffi_except_constructors

end cvc5

namespace cvc5.Sort

extern! "sort"
  def null : Unit → cvc5.Sort

instance : Inhabited cvc5.Sort := ⟨null ()⟩

extern! "sort"
  /-- Comparison for structural equality. -/
  protected def beq : cvc5.Sort → cvc5.Sort → Bool

instance : BEq cvc5.Sort := ⟨Sort.beq⟩

extern! "sort"
  /-- Hash function for cvc5 sorts. -/
  protected def hash : cvc5.Sort → UInt64

instance : Hashable cvc5.Sort := ⟨Sort.hash⟩

extern! "sort"

  /-- Get the kind of this sort. -/
  def getKind : cvc5.Sort → SortKind

  /-- Determine if this is the integer sort (SMT-LIB: `Int`). -/
  def isInteger : cvc5.Sort → Bool

  /-- Determine if this is a function sort. -/
  protected def isFunction : cvc5.Sort → Bool

  /-- A string representation of this sort. -/
  protected def toString : cvc5.Sort → String

/-- Get the symbol of this sort.

The symbol of this sort is the string that was provided when consrtucting it *via* one of
`Solver.mkUninterpretedSort`, `Solver.mkUnresolvedSort`, or
`Solver.mkUninterpretedSortConstructorSort`.
-/
extern_def!? "sort"
  getSymbol : cvc5.Sort → Except Error String

/-- The domain sorts of a function sort. -/
extern_def!? "sort"
  getFunctionDomainSorts : cvc5.Sort → Except Error (Array cvc5.Sort)

/-- The codomain sort of a function sort. -/
extern_def!? "sort"
  getFunctionCodomainSort : cvc5.Sort → Except Error cvc5.Sort

/-- The bit-width of the bit-vector sort. -/
extern_def!? "sort"
  getBitVectorSize : cvc5.Sort → Except Error UInt32

instance : ToString cvc5.Sort := ⟨Sort.toString⟩
instance : Repr cvc5.Sort := ⟨fun self _ => self.toString⟩

end cvc5.Sort

namespace cvc5.Op

extern! "op"
  def null : Unit → Op

instance : Inhabited Op := ⟨null ()⟩

extern! "op"
  /-- Syntactic equality operator. -/
  protected def beq : Op → Op → Bool

instance : BEq Op := ⟨Op.beq⟩

extern! "op"

  /-- Get the kind of this operator. -/
  def getKind : Op → Kind

  /-- Determine if this operator is nullary. -/
  def isNull : Op → Bool

  /-- Determine if this operator is indexed. -/
  def isIndexed : Op → Bool

  /-- Get the number of indices of this operator. -/
  def getNumIndices : Op → Nat

  /-- Get the index at position `i` of an indexed operator. -/
  protected def get : (op : Op) → Fin op.getNumIndices → Term

  /-- Get the string representation of this operator. -/
  protected def toString : Op → String

instance : GetElem Op Nat Term fun op i => i < op.getNumIndices where
  getElem op i h := op.get ⟨i, h⟩

instance : ToString Op := ⟨Op.toString⟩

end Op

namespace Term

extern! "term"
  def null : Unit → Term

instance : Inhabited Term := ⟨null ()⟩

extern! "term"
  /-- Syntactic equality operator. -/
  protected def beq : Term → Term → Bool

instance : BEq Term := ⟨Term.beq⟩

extern! "hash"
  /-- Hash function for terms. -/
  protected def hash : Term → UInt64

instance : Hashable Term := ⟨Term.hash⟩

extern! "term"

  /-- Determine if this term is nullary. -/
  def isNull : Term → Bool

  /-- Get the kind of this term. -/
  def getKind : Term → Kind

  /-- Get the sort of this term. -/
  def getSort : Term → cvc5.Sort

  /-- Determine if this term has an operator. -/
  def hasOp : Term → Bool

  /-- Determine if this term has a symbol (a name).

  For example, free constants and variables have symbols.
  -/
  def hasSymbol : Term → Bool

  /-- Get the id of this term. -/
  def getId : Term → Nat

  /-- Get the number of children of this term. -/
  def getNumChildren : Term → Nat

  /-- Is this term a skolem? -/
  def isSkolem : Term → Bool

  /-- Get the child term of this term at a given index. -/
  protected def get : (t : Term) → Fin t.getNumChildren → Term

/-- Get the operator of a term with an operator.

Requires that this term has an operator (see `hasOp`).
-/
extern_def!? "term" getOp : Term → Except Error Op

/-- Get the value of a Boolean term as a native Boolean value.

Requires `term` to have sort Bool.
-/
extern_def!? "term" getBooleanValue : Term → Except Error Bool

/-- Get the string representation of a bit-vector value.

Requires `term` to have a bit-vector sort.

- `base`: `2` for binary, `10` for decimal, and `16` for hexadecimal.
-/
extern_def!? "term" getBitVectorValue : Term → UInt32 → Except Error String

/-- Get the native integral value of an integral value. -/
extern_def!? "term" getIntegerValue : Term → Except Error Int

/-- Get the native rational value of a real, rational-compatible value. -/
extern_def!? "term" getRationalValue : Term → Except Error Lean.Rat

/-- Get the symbol of this term.

Requires that this term has a symbol (see `hasSymbol`).

The symbol of the term is the string that was provided when constructing it *via*
`TermManager.mkConst` or `TermManager.mkVar`.
-/
extern_def!? "term" getSymbol : Term → Except Error String

/-- Get skolem identifier of this term.

Requires `isSkolem`.
-/
extern_def!? "term" getSkolemId : Term → Except Error SkolemId

/-- Get the skolem indices of this term.

Requires `isSkolem`.

Returns the skolem indices of this term. This is a list of terms that the skolem function is
indexed by. For example, the array diff skolem `SkolemId.ARRAY_DEQ_DIFF` is indexed by two arrays.
-/
extern_def!? "term" getSkolemIndices : Term → Except Error (Array Term)

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

/-- Get the children of a term. -/
def getChildren (t : Term) : Array Term := Id.run do
  let mut cts := #[]
  for ct in t do
    cts := cts.push ct
  cts

/-- Boolean negation. -/
protected extern_def!? "term" not : Term → Except Error Term

/-- Boolean and. -/
protected extern_def!? "term" and : Term → Term → Except Error Term

/-- Boolean or. -/
protected extern_def!? "term" or : Term → Term → Except Error Term

extern! "term"
  /-- A string representation of this term. -/
  protected def toString : Term → String

instance : ToString Term := ⟨Term.toString⟩

end Term

namespace Proof

extern! "proof"
  def null : Unit → Proof

instance : Inhabited Proof := ⟨null ()⟩

extern! "proof"
  /-- The proof rule used by the root step of the proof. -/
  def getRule : Proof → ProofRule

  /-- The proof rewrite rule used by the root step of the proof. -/
  def getRewriteRule : Proof → ProofRewriteRule

  /-- The conclusion of the root step of the proof. -/
  def getResult : Proof → Term

  /-- The premises of the root step of the proof. -/
  def getChildren : Proof → Array Proof

  /-- The arguments of the root step of the proof as a vector of terms.

  Some of those terms might be strings.
  -/
  def getArguments : Proof → Array Term

  /-- Operator overloading for referential equality of two proofs. -/
  protected def beq : Proof → Proof → Bool

instance : BEq Proof := ⟨Proof.beq⟩

extern! "proof"
  /-- Hash function for proofs. -/
  protected def hash : Proof → UInt64

instance : Hashable Proof := ⟨Proof.hash⟩

end Proof

namespace TermManager

extern! "termManager"
  /-- Constructor. -/
  def new : BaseIO TermManager

  /-- Get the Boolean sort. -/
  def getBooleanSort : TermManager → cvc5.Sort

  /-- Get the Integer sort. -/
  def getIntegerSort : TermManager → cvc5.Sort

  /-- Get the Real sort. -/
  def getRealSort : TermManager → cvc5.Sort

  /-- Get the regular expression sort. -/
  def getRegExpSort : TermManager → cvc5.Sort

  /-- Get the rounding mode sort. -/
  def getRoundingModeSort : TermManager → cvc5.Sort

  /-- Get the string sort. -/
  def getStringSort : TermManager → cvc5.Sort

/-- Create an array sort.

- `indexSort` The array index sort.
- `elemSort` The array element sort.
-/
extern_def!? "termManager"
  mkArraySort : TermManager → (indexSort elemSort : cvc5.Sort) → Except Error cvc5.Sort

/-- Create a bit-vector sort.

- `size` The bit-width of the bit-vector sort.
-/
extern_def!? "termManager"
  mkBitVectorSort : TermManager → (size : UInt32) → Except Error cvc5.Sort

/-- Create a floating-point sort.

- `exp` The bit-width of the exponent of the floating-point sort.
- `sig` The bit-width of the significand of the floating-point sort.
-/
extern_def!? "termManager"
  mkFloatingPointSort : TermManager → (exp sig : UInt32) → Except Error cvc5.Sort

/-- Create function sort.

- `sorts` The sort of the function arguments.
- `codomain` The sort of the function return value.
-/
extern_def!? "termManager"
  mkFunctionSort
  : TermManager → (sorts : Array cvc5.Sort) → (codomain : cvc5.Sort) → Except Error cvc5.Sort

extern! "termManager"
  /-- Create a Boolean constant.

  - `b`: The Boolean constant.
  -/
  def mkBoolean : TermManager → Bool → Term

  /-- Create an integer-value term. -/
  private def mkIntegerFromString : TermManager → String → Except Error Term
  with
    mkInteger (tm : TermManager) : Int → Except Error Term :=
      tm.mkIntegerFromString ∘ toString
    mkInteger? := (mkInteger · · |> Except.toOption)
    mkInteger! := (mkInteger · · |> Error.unwrap!)

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

If `args` is empty, the `Op` simply wraps the `cvc5.Kind`. The `Kind` can be used in
`Solver.mkTerm` directly without creating an `Op` first.
-/
extern_def!? "termManager"
  mkOpOfIndices : TermManager → (kind : Kind) → (args : Array Nat) → Except Error Op

/-- Create operator of kind:

- `Kind.DIVISIBLE` (to support arbitrary precision integers)

See `cvc5.Kind` for a description of the parameters.

- `kind` The kind of the operator.
- `arg` The string argument to this operator.
-/
extern_def!? "termManager"
  mkOpOfString : TermManager → (kind : Kind) → (arg : String) → Except Error Op

/-- Create n-ary term of given kind.

- `kind` The kind of the term.
- `children` The children of the term.
-/
extern_def!? "termManager"
  mkTerm : TermManager → (kind : Kind) → (children : Array Term := #[]) → Except Error Term

/-- Create n-ary term of given kind from a given operator.

Create operators with `mkOp`.

- `op` The operator.
- `children` The children of the term.
-/
extern_def!? "termManager"
  mkTermOfOp : TermManager → (op : Op) → (children : Array Term := #[]) → Except Error Term

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
private def errorOfString (msg : String) : SolverT m α := throw (.error msg)

extern! "solver"

  /-- Constructor.

  Constructs solver instance from a given term manager instance.

  - `tm`: The associated term manager.
  -/
  private def new : TermManager → Solver

  /-- Get a string representation of the version of this solver. -/
  def getVersion : SolverT m String

  /-- Set option.

  - `option`: The option name.
  - `value`: The option value.
  -/
  def setOption (option value : String) : SolverT m Unit

  /-- Assert a formula.

  - `term`: The formula to assert.
  -/
  def assertFormula : Term → SolverT m Unit

  /-- Check satisfiability. -/
  def checkSat : SolverT m Result

  /-- Get a proof associated with the most recent call to `checkSat`.

  Requires to enable option `produce-proofs`.
  -/
  def getProof : SolverT m (Array Proof)

  /-- Prints a proof as a string in a selected proof format mode.

  Other aspects of printing are taken from the solver options.

  - `proof`: A proof, usually obtained from `getProof`.
  -/
  def proofToString : Proof → SolverT m String

  /-- Parse a string containing SMT-LIB commands.

  Commands that produce a result such as `(check-sat)`, `(get-model)`, ... are executed but the
  results are ignored.
  -/
  def parse : String → SolverT m Unit

/-- Run a `query` given a term manager `tm`. -/
def run (tm : TermManager) (query : SolverT m α) : m (Except Error α) :=
  return match ← ExceptT.run query (new tm) with
  | (.ok x, _) => .ok x
  | (.error e, _) => .error e

end Solver

end cvc5
