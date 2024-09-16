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
  | error (msg : String)
  | recoverable (msg : String)
  | unsupported (msg : String)
  | option (msg : String)
deriving Repr

private opaque SolverImpl : NonemptyType.{0}

def Solver : Type := SolverImpl.type

instance Solver.instNonemptySolver : Nonempty Solver := SolverImpl.property

abbrev SolverT m := ExceptT Error (StateT Solver m)

abbrev SolverM := SolverT IO

namespace Error

protected def toString : Error → String :=
  toString ∘ repr

def unwrap! [Inhabited α] : Except Error α → α
| .ok a => a
| .error e => panic! e.toString

instance : ToString Error :=
  ⟨Error.toString⟩

end Error

namespace Result

extern! "result"
  def isSat : Result → Bool
  def isUnsat : Result → Bool
  def isUnknown : Result → Bool
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
  protected def beq : cvc5.Sort → cvc5.Sort → Bool

instance : BEq cvc5.Sort := ⟨Sort.beq⟩

extern! "sort"
  protected def hash : cvc5.Sort → UInt64

instance : Hashable cvc5.Sort := ⟨Sort.hash⟩

extern! "sort"
  def getKind : cvc5.Sort → SortKind
  def isInteger : cvc5.Sort → Bool
  protected def toString : cvc5.Sort → String

/-- The domain sorts of a function sort. -/
extern_def!? "sort"
  getSymbol : cvc5.Sort → Except Error String

/-- The domain sorts of a function sort. -/
extern_def!? "sort"
  getFunctionDomainSorts : cvc5.Sort → Except Error (Array cvc5.Sort)

/-- The codomain sort of a function sort. -/
extern_def!? "sort"
  getFunctionCodomainSort : cvc5.Sort → Except Error cvc5.Sort

/-- The codomain sort of a function sort. -/
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
  protected def beq : Op → Op → Bool

instance : BEq Op := ⟨Op.beq⟩

extern! "op"
  def getKind : Op → Kind
  def isNull : Op → Bool
  def isIndexed : Op → Bool
  def getNumIndices : Op → Nat
  protected def get : (op : Op) → Fin op.getNumIndices → Term
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
  protected def beq : Term → Term → Bool

instance : BEq Term := ⟨Term.beq⟩

extern! "hash"
  protected def hash : Term → UInt64

instance : Hashable Term := ⟨Term.hash⟩

extern! "term"
  def isNull : Term → Bool
  def getKind : Term → Kind
  def getSort : Term → cvc5.Sort
  def getOp : Term → Op
  def hasSymbol : Term → Bool
  def getId : Term → Nat
  def getNumChildren : Term → Nat
  def isSkolem : Term → Bool
  protected def get : (t : Term) → Fin t.getNumChildren → Term

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
  protected def toString : Term → String

instance : ToString Term := ⟨Term.toString⟩

end Term

namespace Proof

extern! "proof"
  def null : Unit → Proof

instance : Inhabited Proof := ⟨null ()⟩

extern! "proof"
  def getRule : Proof → ProofRule
  def getRewriteRule : Proof → ProofRewriteRule
  def getResult : Proof → Term
  def getChildren : Proof → Array Proof
  def getArguments : Proof → Array Term
  protected def beq : Proof → Proof → Bool

instance : BEq Proof := ⟨Proof.beq⟩

extern! "proof"
  protected def hash : Proof → UInt64

instance : Hashable Proof := ⟨Proof.hash⟩

end Proof

namespace TermManager

extern! "termManager"
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

@[export solver_val]
private def val (a : α) : SolverT m α := pure a

@[export solver_err]
private def err (e : Error) : SolverT m α := throw e

extern! "solver"
  private def new : TermManager → Solver
  def getVersion : SolverT m String
  def setOption (option value : String) : SolverT m Unit
  def assertFormula : Term → SolverT m Unit
  def checkSat : SolverT m Result
  def getProof : SolverT m (Array Proof)
  def proofToString : Proof → SolverT m String
  def parse : String → SolverT m Unit

def run (tm : TermManager) (query : SolverT m α) : m (Except Error α) :=
  return match ← ExceptT.run query (new tm) with
  | (.ok x, _) => .ok x
  | (.error e, _) => .error e

end Solver

end cvc5
