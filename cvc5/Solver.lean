/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Adrien Champion
-/

import Std.Internal.Rat

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

/-- True if this result is from a satisfiable `checkSat` or `checkSatAssuming` query. -/
extern_def isSat : Result → Bool

/-- True if this result is from a unsatisfiable `checkSat` or `checkSatAssuming` query. -/
extern_def isUnsat : Result → Bool

/-- True if this result is from a `checkSat` or `checkSatAssuming` query and cvc5 was not able to
determine (un)satisfiability.
-/
extern_def isUnknown : Result → Bool

/-- A string representation of this result. -/
protected extern_def toString : Result → String

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
@[export except_ok_u16]
private def mkExceptOkU16 : UInt16 → Except Error UInt16 :=
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

/-- The null sort. -/
extern_def null : Unit → cvc5.Sort

instance : Inhabited cvc5.Sort := ⟨null ()⟩

/-- Comparison for structural equality. -/
protected extern_def beq : cvc5.Sort → cvc5.Sort → Bool

instance : BEq cvc5.Sort := ⟨Sort.beq⟩

/-- Less than comparison. -/
protected extern_def blt : cvc5.Sort → cvc5.Sort → Bool

/-- Greater than comparison. -/
protected extern_def bgt : cvc5.Sort → cvc5.Sort → Bool

/-- Less than or equal comparison. -/
protected extern_def ble : cvc5.Sort → cvc5.Sort → Bool

/-- Greater than or equal comparison. -/
protected extern_def bge : cvc5.Sort → cvc5.Sort → Bool

/-- Comparison of two sorts. -/
protected def compare (s1 s2 : cvc5.Sort) : Ordering :=
  if s1.beq s2 then .eq
  else if s1.bgt s2 then .gt
  else .lt

instance : Ord cvc5.Sort := ⟨Sort.compare⟩

instance : LT cvc5.Sort where
  lt := (Sort.blt · ·)

instance : DecidableLT cvc5.Sort :=
  fun s1 s2 => if h : s1.blt s2 then .isTrue h else .isFalse h

instance : LE cvc5.Sort where
  le := (Sort.ble · ·)

instance : DecidableLE cvc5.Sort :=
  fun s1 s2 => if h : s1.ble s2 then .isTrue h else .isFalse h

/-- Hash function for cvc5 sorts. -/
protected extern_def hash : cvc5.Sort → UInt64

instance : Hashable cvc5.Sort := ⟨Sort.hash⟩

/-- Get the kind of this sort. -/
extern_def getKind : cvc5.Sort → SortKind

/-- Determine if this is the null sort (`cvc5.Sort`). -/
extern_def isNull : cvc5.Sort → Bool

/-- Determine if this is the Boolean sort (SMT-LIB: `Bool`). -/
extern_def isBoolean : cvc5.Sort → Bool

/-- Determine if this is the Integer sort (SMT-LIB: `Int`). -/
extern_def isInteger : cvc5.Sort → Bool

/-- Determine if this is the Real sort (SMT-LIB: `Real`). -/
extern_def isReal : cvc5.Sort → Bool

/-- Determine if this is the String sort (SMT-LIB: `String`). -/
extern_def isString : cvc5.Sort → Bool

/-- Determine if this is the regular expression sort (SMT-LIB: `RegLan`). -/
extern_def isRegExp : cvc5.Sort → Bool

/-- Determine if this is the rounding mode sort (SMT-LIB: `RoundingMode`). -/
extern_def isRoundingMode : cvc5.Sort → Bool

/-- Determine if this is a bit-vector sort (SMT-LIB: `(_ BitVec i)`). -/
extern_def isBitVector : cvc5.Sort → Bool

/-- Determine if this is a floating-point sort (SMT-LIB: `(_ FloatingPoint eb sb)`). -/
extern_def isFloatingPoint : cvc5.Sort → Bool

/-- Determine if this is a datatype sort. -/
extern_def isDatatype : cvc5.Sort → Bool

/-- Determine if this is a datatype constructor sort. -/
extern_def isDatatypeConstructor : cvc5.Sort → Bool

/-- Determine if this is a datatype selector sort. -/
extern_def isDatatypeSelector : cvc5.Sort → Bool

/-- Determine if this is a datatype tester sort. -/
extern_def isDatatypeTester : cvc5.Sort → Bool

/-- Determine if this is a datatype updater sort. -/
extern_def isDatatypeUpdater : cvc5.Sort → Bool

/-- Determine if this is a function sort. -/
extern_def isFunction : cvc5.Sort → Bool

/-- Determine if this is a predicate sort.

A predicate sort is a function sort that maps to the Boolean sort. All predicate sorts are also
function sorts.
-/
extern_def isPredicate : cvc5.Sort → Bool

/-- Determine if this is a tuple sort. -/
extern_def isTuple : cvc5.Sort → Bool

/-- Determine if this is a nullable sort. -/
extern_def isNullable : cvc5.Sort → Bool

/-- Determine if this is a record sort.

**Warning**: this function is experimental and may change in future versions.
-/
extern_def isRecord : cvc5.Sort → Bool

/-- Determine if this is an array sort. -/
extern_def isArray : cvc5.Sort → Bool

/-- Determine if this is a finite field sort. -/
extern_def isFiniteField : cvc5.Sort → Bool

/-- Determine if this is a Set sort. -/
extern_def isSet : cvc5.Sort → Bool

/-- Determine if this is a Bag sort. -/
extern_def isBag : cvc5.Sort → Bool

/-- Determine if this is a Sequence sort. -/
extern_def isSequence : cvc5.Sort → Bool

/-- Determine if this is an abstract sort. -/
extern_def isAbstract : cvc5.Sort → Bool

/-- Determine if this is an uninterpreted sort. -/
extern_def isUninterpretedSort : cvc5.Sort → Bool

/-- Determine if this is an uninterpreted sort constructor.

An uninterpreted sort constructor has arity `> 0` and can be instantiated to construct uninterpreted
sorts with given sort parameters.
-/
extern_def isUninterpretedSortConstructor : cvc5.Sort → Bool

/-- Determine if this is an instantiated (parametric datatype or uninterpreted sort constructor)
sort.

An instantiated sort is a sort that has been constructed from instantiating a sort with sort
arguments --- see also `cvc5.Sort.instantiate`.
-/
extern_def isInstantiated : cvc5.Sort → Bool

/-- A string representation of this sort. -/
protected extern_def toString : cvc5.Sort → String

/-- Determine if this term has a symbol (a name).

For example, free constants and variables have symbols.
-/
extern_def!? hasSymbol : cvc5.Sort → Except Error Bool

/-- Get the symbol of this sort.

The symbol of this sort is the string that was provided when consrtucting it *via* one of
`Solver.mkUninterpretedSort`, `Solver.mkUnresolvedSort`, or
`Solver.mkUninterpretedSortConstructorSort`.
-/
extern_def!? getSymbol : cvc5.Sort → Except Error String

/-- The arity of a function sort. -/
extern_def!? getFunctionArity : cvc5.Sort → Except Error Nat

/-- The domain sorts of a function sort. -/
extern_def!? getFunctionDomainSorts : cvc5.Sort → Except Error (Array cvc5.Sort)

/-- The codomain sort of a function sort. -/
extern_def!? getFunctionCodomainSort : cvc5.Sort → Except Error cvc5.Sort

/-- The array index sort of an array index. -/
extern_def!? getArrayIndexSort : cvc5.Sort → Except Error cvc5.Sort

/-- The array element sort of an array index. -/
extern_def!? getArrayElementSort : cvc5.Sort → Except Error cvc5.Sort

/-- The element sort of a set sort. -/
extern_def!? getSetElementSort : cvc5.Sort → Except Error cvc5.Sort

/-- The element sort of a bag sort. -/
extern_def!? getBagElementSort : cvc5.Sort → Except Error cvc5.Sort

/-- The element sort of a sequence sort. -/
extern_def!? getSequenceElementSort : cvc5.Sort → Except Error cvc5.Sort

/-- The sort kind of an abstract sort, which denotes the kind of sorts that this abstract sort
denotes.
-/
extern_def!? getAbstractedKind : cvc5.Sort → Except Error SortKind

/-- The arity of an uninterpreted sort constructor sort. -/
extern_def!? getUninterpretedSortConstructorArity : cvc5.Sort → Except Error UInt32

/-- The bit-width of the bit-vector sort. -/
extern_def!? getBitVectorSize : cvc5.Sort → Except Error UInt32

/-- The size of the finite field sort. -/
extern_def!? getFiniteFieldSize : cvc5.Sort → Except Error Nat

/-- The bit-width of the exponent of the floating-point sort. -/
extern_def!? getFloatingPointExponentSize : cvc5.Sort → Except Error UInt32

/-- The width of the significand of the floating-point sort. -/
extern_def!? getFloatingPointSignificandSize : cvc5.Sort → Except Error UInt32

/-- The length of a tuple sort. -/
extern_def!? getTupleLength : cvc5.Sort → Except Error UInt32

/-- The element sorts of a tuple sort. -/
extern_def!? getTupleSorts : cvc5.Sort → Except Error (Array cvc5.Sort)

/-- The element sort of a nullable sort. -/
extern_def!? getNullableElementSort : cvc5.Sort → Except Error cvc5.Sort

/-- Get the associated uninterpreted sort constructor of an instantiated uninterpreted sort. -/
extern_def!? getUninterpretedSortConstructor : cvc5.Sort → Except Error cvc5.Sort

/-- Instantiate a parameterized datatype sort or uninterpreted sort constructor sort.

Create sort parameters with `TermManager.mkParamSort symbol`.

- `params` The list of sort parameters to instantiate with.
-/
extern_def!? instantiate : cvc5.Sort → (params : Array cvc5.Sort) → Except Error cvc5.Sort

/-- Simultaneous substitution of Sorts.

Note that this replacement is applied during a pre-order traversal and only once to the sort. It is not run until fix point. In the case that `sorts` contains duplicates, the replacement earliest in
the vector takes priority.

**Warning:** This function is experimental and may change in future versions.

- `sorts` The sub-sorts to be substituted within this sort.
- `replacements` The sort replacing the substituted sub-sorts.
-/
extern_def!? substitute
: cvc5.Sort → (sorts : Array cvc5.Sort) → (replacements : Array cvc5.Sort) → Except Error cvc5.Sort

instance : ToString cvc5.Sort := ⟨Sort.toString⟩
instance : Repr cvc5.Sort := ⟨fun self _ => self.toString⟩

end cvc5.Sort

namespace cvc5.Op

/-- The null operator. -/
extern_def null : Unit → Op

instance : Inhabited Op := ⟨null ()⟩

/-- Syntactic equality operator. -/
protected extern_def beq : Op → Op → Bool

instance : BEq Op := ⟨Op.beq⟩

/-- Get the kind of this operator. -/
extern_def getKind : Op → Kind

/-- Determine if this operator is nullary. -/
extern_def isNull : Op → Bool

/-- Determine if this operator is indexed. -/
extern_def isIndexed : Op → Bool

/-- Get the number of indices of this operator. -/
extern_def getNumIndices : Op → Nat

/-- Get the index at position `i` of an indexed operator. -/
protected extern_def get : (op : Op) → Fin op.getNumIndices → Term

/-- Get the string representation of this operator. -/
protected extern_def toString : Op → String

instance : GetElem Op Nat Term fun op i => i < op.getNumIndices where
  getElem op i h := op.get ⟨i, h⟩

instance : ToString Op := ⟨Op.toString⟩

end Op

namespace Term

/-- The null term. -/
extern_def null : Unit → Term

instance : Inhabited Term := ⟨null ()⟩

/-- Syntactic equality operator. -/
protected extern_def beq : Term → Term → Bool

instance : BEq Term := ⟨Term.beq⟩

protected extern_def hash : Term → UInt64

instance : Hashable Term := ⟨Term.hash⟩

/-- Determine if this term is nullary. -/
extern_def isNull : Term → Bool

/-- Get the kind of this term. -/
extern_def getKind : Term → Kind

/-- Get the sort of this term. -/
extern_def getSort : Term → cvc5.Sort

/-- Determine if this term has an operator. -/
extern_def hasOp : Term → Bool

/-- Determine if this term has a symbol (a name).

For example, free constants and variables have symbols.
-/
extern_def hasSymbol : Term → Bool

/-- Get the id of this term. -/
extern_def getId : Term → Nat

/-- Get the number of children of this term. -/
extern_def getNumChildren : Term → Nat

/-- Is this term a skolem? -/
extern_def isSkolem : Term → Bool

/-- Get the child term of this term at a given index. -/
protected extern_def get : (t : Term) → Fin t.getNumChildren → Term

/-- Get the operator of a term with an operator.

Requires that this term has an operator (see `hasOp`).
-/
extern_def!? getOp : Term → Except Error Op

/-- Get the value of a Boolean term as a native Boolean value.

Requires `term` to have sort Bool.
-/
extern_def!? getBooleanValue : Term → Except Error Bool

/-- Get the string representation of a bit-vector value.

Requires `term` to have a bit-vector sort.

- `base`: `2` for binary, `10` for decimal, and `16` for hexadecimal.
-/
extern_def!? getBitVectorValue : Term → UInt32 → Except Error String

/-- Get the native integral value of an integral value. -/
extern_def!? getIntegerValue : Term → Except Error Int

/-- Get the native rational value of a real, rational-compatible value. -/
extern_def!? getRationalValue : Term → Except Error Std.Internal.Rat

/-- Get the symbol of this term.

Requires that this term has a symbol (see `hasSymbol`).

The symbol of the term is the string that was provided when constructing it *via*
`TermManager.mkConst` or `TermManager.mkVar`.
-/
extern_def!? getSymbol : Term → Except Error String

/-- Get skolem identifier of this term.

Requires `isSkolem`.
-/
extern_def!? getSkolemId : Term → Except Error SkolemId

/-- Get the skolem indices of this term.

Requires `isSkolem`.

Returns the skolem indices of this term. This is a list of terms that the skolem function is indexed
by. For example, the array diff skolem `SkolemId.ARRAY_DEQ_DIFF` is indexed by two arrays.
-/
extern_def!? getSkolemIndices : Term → Except Error (Array Term)

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
protected extern_def!? not : Term → Except Error Term

/-- Boolean and. -/
protected extern_def!? and : Term → Term → Except Error Term

/-- Boolean or. -/
protected extern_def!? or : Term → Term → Except Error Term

/-- A string representation of this term. -/
protected extern_def toString : Term → String

instance : ToString Term := ⟨Term.toString⟩

end Term

namespace Proof

/-- The null proof. -/
extern_def null : Unit → Proof

instance : Inhabited Proof := ⟨null ()⟩

/-- Get the proof rule used by the root step of the root. -/
extern_def getRule : Proof → ProofRule

/-- Get the proof rewrite rule used by the root step of the proof.

Requires that `getRule` does not return `ProofRule.DSL_REWRITE` or `ProofRule.REWRITE`.
-/
extern_def!? getRewriteRule : Proof → Except Error ProofRewriteRule

/-- The conclusion of the root step of the proof. -/
extern_def getResult : Proof → Term

/-- The premises of the root step of the proof. -/
extern_def getChildren : Proof → Array Proof

/-- The arguments of the root step of the proof as a vector of terms.

Some of those terms might be strings.
-/
extern_def getArguments : Proof → Array Term

/-- Operator overloading for referential equality of two proofs. -/
protected extern_def beq : Proof → Proof → Bool

instance : BEq Proof := ⟨Proof.beq⟩

/-- Hash function for proofs. -/
protected extern_def hash : Proof → UInt64

instance : Hashable Proof := ⟨Proof.hash⟩

end Proof

namespace TermManager

/-- Constructor. -/
extern_def new : BaseIO TermManager

/-- Get the Boolean sort. -/
extern_def getBooleanSort : TermManager → cvc5.Sort

/-- Get the Integer sort. -/
extern_def getIntegerSort : TermManager → cvc5.Sort

/-- Get the Real sort. -/
extern_def getRealSort : TermManager → cvc5.Sort

/-- Get the regular expression sort. -/
extern_def getRegExpSort : TermManager → cvc5.Sort

/-- Get the rounding mode sort. -/
extern_def getRoundingModeSort : TermManager → cvc5.Sort

/-- Get the string sort. -/
extern_def getStringSort : TermManager → cvc5.Sort

/-- Create an array sort.

- `indexSort` The array index sort.
- `elemSort` The array element sort.
-/
extern_def!? mkArraySort : TermManager → (indexSort elemSort : cvc5.Sort) → Except Error cvc5.Sort

/-- Create a bit-vector sort.

- `size` The bit-width of the bit-vector sort.
-/
extern_def!? mkBitVectorSort : TermManager → (size : UInt32) → Except Error cvc5.Sort

/-- Create a floating-point sort.

- `exp` The bit-width of the exponent of the floating-point sort.
- `sig` The bit-width of the significand of the floating-point sort.
-/
extern_def!? mkFloatingPointSort : TermManager → (exp sig : UInt32) → Except Error cvc5.Sort

/-- Create a finite-field sort from a given string of base n.

- `size` The modulus of the field. Must be a prime.
-/
private extern_def mkFiniteFieldSortFromString : TermManager → (size : String) → (base : UInt32 := 10) → Except Error cvc5.Sort

@[inherit_doc mkFiniteFieldSortFromString]
abbrev mkFiniteFieldSort (tm : TermManager) : (size : Nat) → Except Error cvc5.Sort :=
  (tm.mkFiniteFieldSortFromString · 10) ∘ toString
@[inherit_doc mkFiniteFieldSortFromString]
abbrev mkFiniteFieldSort! (tm : TermManager) : (size : Nat) → cvc5.Sort :=
  Error.unwrap! ∘ (tm.mkFiniteFieldSortFromString · 10) ∘ toString
@[inherit_doc mkFiniteFieldSortFromString]
abbrev mkFiniteFieldSort? (tm : TermManager) : (size : Nat) → Option cvc5.Sort :=
  Except.toOption ∘ (tm.mkFiniteFieldSortFromString · 10) ∘ toString

/-- Create function sort.

- `sorts` The sort of the function arguments.
- `codomain` The sort of the function return value.
-/
extern_def!? mkFunctionSort
: TermManager → (sorts : Array cvc5.Sort) → (codomain : cvc5.Sort) → Except Error cvc5.Sort

/-- Create a predicate sort.

This is equivalent to calling `mkFunctionSort` with Boolean sort as the codomain.

- `sorts` The list of sorts of the predicate.
-/
extern_def!? mkPredicateSort : TermManager → (sorts : Array cvc5.Sort) → Except Error cvc5.Sort

/-- Create a tuple sort.

- `sorts` The sorts of the elements of the tuple.
-/
extern_def!? mkTupleSort : TermManager → (sorts : Array cvc5.Sort) → Except Error cvc5.Sort

/-- Create an uninterpreted sort constructor sort.

An uninterpreted sort constructor is an uninterpreted sort with arity > 0.

- `arity` The arity of the sort (must be > 0).
- `symbol` The symbol of the sort.
-/
extern_def!? mkUninterpretedSortConstructorSort
: TermManager → (arity : Nat) → (symbol : String) → Except Error cvc5.Sort

/-- Create a set parameter.

- `elemSort` The sort of the set elements.
-/
extern_def!? mkSetSort : TermManager → (sort : cvc5.Sort) → Except Error cvc5.Sort

/-- Create a set parameter.

- `elemSort` The sort of the set elements.
-/
extern_def!? mkBagSort : TermManager → (sort : cvc5.Sort) → Except Error cvc5.Sort

/-- Create a set parameter.

- `elemSort` The sort of the set elements.
-/
extern_def!? mkSequenceSort : TermManager → (sort : cvc5.Sort) → Except Error cvc5.Sort

/-- Create an abstract sort. An abstract sort represents a sort for a given kind whose parameters
and arguments are unspecified.

The kind `k` must be the kind of a sort that can be abstracted, *i.e.* a sort that has indices or
arguments sorts. For example, `SortKind.ARRAY_SORT` and `SortKind.BITVECTOR_SORT` can be passed as
the kind `k` to this function, while `SortKind.INTEGER_SORT` and `SortKind.STRING_SORT` cannot.

**NB:** Providing the kind `SortKind.ABSTRACT_SORT` as an argument to this function returns the
(fully) unspecified sort, denoted `?`.

**NB:** Providing a kind `k` that has no indices and a fixed arity of argument sorts will return the
sort of kind `k` whose arguments are the unspecified sort. For example, `mkAbstractSort
SortKind.ARRAY_SORT` will return the sort `(ARRAY_SORT ? ?)` instead of the abstract sort whose
abstract kind is `SortKind.ARRAY_SORT`.
-/
extern_def!? mkAbstractSort : TermManager → (k : SortKind) → Except Error cvc5.Sort

/-- Create an uninterpreted sort.

- `symbol` The name of the sort.
-/
extern_def mkUninterpretedSort : TermManager → (symbol : String) → cvc5.Sort

/-- Create a nullable sort.

- `sort` The sort of the element of the nullable.
-/
extern_def!? mkNullableSort : TermManager → (sort : cvc5.Sort) → Except Error cvc5.Sort

/-- Create a sort parameter.

- `symbol` The name of the sort.

**Warning**: This function is experimental and may change in future versions.
-/
extern_def mkParamSort : TermManager → (symbol : String) → cvc5.Sort

/-- Create a Boolean constant.

- `b`: The Boolean constant.
-/
extern_def mkBoolean : TermManager → (b : Bool) → Term

/-- Create an integer-value term. -/
private extern_def mkIntegerFromString : TermManager → String → Except Error Term
with
  mkInteger (tm : TermManager) : Int → Term :=
    Error.unwrap! ∘ tm.mkIntegerFromString ∘ toString

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
extern_def!? mkOpOfIndices : TermManager → (kind : Kind) → (args : Array Nat := #[]) → Except Error Op

@[inherit_doc mkOpOfIndices]
abbrev mkOp := @mkOpOfIndices
@[inherit_doc mkOpOfIndices!]
abbrev mkOp! := @mkOpOfIndices!
@[inherit_doc mkOpOfIndices?]
abbrev mkOp? := @mkOpOfIndices?

/-- Create operator of kind:

- `Kind.DIVISIBLE` (to support arbitrary precision integers)

See `cvc5.Kind` for a description of the parameters.

- `kind` The kind of the operator.
- `arg` The string argument to this operator.
-/
extern_def!? mkOpOfString : TermManager → (kind : Kind) → (arg : String) → Except Error Op

/-- Create n-ary term of given kind.

- `kind` The kind of the term.
- `children` The children of the term.
-/
extern_def!? mkTerm : TermManager → (kind : Kind) → (children : Array Term := #[]) → Except Error Term

/-- Create n-ary term of given kind from a given operator.

Create operators with `mkOp`.

- `op` The operator.
- `children` The children of the term.
-/
extern_def!? mkTermOfOp : TermManager → (op : Op) → (children : Array Term := #[]) → Except Error Term

/-- **THIS FUNCTION MUST NOT BE EXPOSED.**

**It produces a different (fresh) term every time it's called which is really bad for purity.**

Create a free constant.

Note that the returned term is always fresh, even if the same arguments were provided on a
previous call to `mkConst`.

- `sort` The sort of the constant.
- `symbol` The name of the constant (optional).
-/
private
def mkConst (_ : TermManager) (_ : cvc5.Sort) (_ : String := "") : Term :=
  panic! "illegal call to `cvc5.TermManager.mkConst"

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

/-- Constructor.

Constructs solver instance from a given term manager instance.

- `tm`: The associated term manager.
-/
private extern_def new : TermManager → Solver

/-- Get a string representation of the version of this solver. -/
extern_def getVersion : SolverT m String

/-- Set option.

- `option`: The option name.
- `value`: The option value.
-/
extern_def setOption (option value : String) : SolverT m Unit

/-- Remove all assertions. -/
extern_def resetAssertions : SolverT m Unit

/-- Set logic.

- `logic`: The logic to set.
-/
extern_def setLogic : (logic : String) → SolverT m Unit

/-- Simplify a term or formula based on rewriting and (optionally) applying substitutions for
solved variables.

If `applySubs` is true, then for example, if `(= x 0)` was asserted to this solver, this function
may replace occurrences of `x` with `0`.

- `t` The term to simplify.
- `applySubs` True to apply substitutions for solved variables.
-/
extern_def simplify : (term : Term) → (applySubs : Bool := false) → SolverT m Term

/--
Declare n-ary function symbol.

SMT-LIB:

\verbatim embed:rst:leading-asterisk
 .. code:: smtlib

     (declare-fun <symbol> ( <sort>* ) <sort>)
 \endverbatim

- `symbol`: The name of the function.
- `sorts`: The sorts of the parameters to this function.
- `sort`: The sort of the return value of this function.
- `fresh`: If true, then this method always returns a new Term. Otherwise, this method will always
  return the same Term for each call with the given sorts and symbol where fresh is false.
-/
extern_def declareFun (symbol : String) (sorts : Array cvc5.Sort) (sort : cvc5.Sort) (fresh := true) : SolverT m Term

/-- Assert a formula.

- `term`: The formula to assert.
-/
extern_def assertFormula : Term → SolverT m Unit

/-- Check satisfiability. -/
extern_def checkSat : SolverT m Result

/-- Check satisfiability assuming the given formulas.

- `assumptions`: The formulas to assume.
-/
extern_def checkSatAssuming : (assumptions : Array Term) → SolverT m Result

/-- Get a proof associated with the most recent call to `checkSat`.

Requires to enable option `produce-proofs`.
-/
extern_def getProof : SolverT m (Array Proof)

/--
Get the values of the given term in the current model.

SMT-LIB:

\verbatim embed:rst:leading-asterisk
.. code:: smtlib

    (get-value ( <term>* ))
\endverbatim

- `terms`: The term for which the value is queried.
-/
extern_def getValue (term : Term) : SolverT m Term

/--
Get the values of the given terms in the current model.

SMT-LIB:

\verbatim embed:rst:leading-asterisk
.. code:: smtlib

    (get-value ( <term>* ))
\endverbatim

- `terms`: The terms for which the values are queried.
-/
extern_def getValues (terms : Array Term) : SolverT m (Array Term)

/-- Prints a proof as a string in a selected proof format mode.

Other aspects of printing are taken from the solver options.

- `proof`: A proof, usually obtained from `getProof`.
-/
extern_def proofToString : Proof → SolverT m String

/-- Parse a string containing SMT-LIB commands.

Commands that produce a result such as `(check-sat)`, `(get-model)`, ... are executed but the
results are ignored.
-/
extern_def parseCommands : String → SolverT m Unit

/-- Run a `query` given a term manager `tm`. -/
def run (tm : TermManager) (query : SolverT m α) : m (Except Error α) :=
  return match ← ExceptT.run query (new tm) with
  | (.ok x, _) => .ok x
  | (.error e, _) => .error e

/-- Run a `query` given a term manager `tm`. -/
def run! [Inhabited α] (tm : TermManager) (query : SolverT m α) : m α := do
  match ← ExceptT.run query (new tm) with
  | (.ok x, _) => return x
  | (.error e, _) => do
    panic! s!"{e}"

end Solver

end cvc5
