/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Adrien Champion
-/

module

meta import cvc5.Init

public import cvc5.Kind
public import cvc5.ProofRule
public import cvc5.SkolemId
public import cvc5.Types

public section

open cvc5.Init

@[export prod_mk_generic]
private def mkProd := @Prod.mk

namespace cvc5

namespace Kind

/-- Produces a string representation. -/
@[extern "kind_toString"]
protected opaque toString : Kind → String

instance : ToString Kind := ⟨Kind.toString⟩

/-- Produces a hash. -/
@[extern "kind_hash"]
protected opaque hash : Kind → UInt64

instance : Hashable Kind := ⟨Kind.hash⟩

end Kind

namespace SortKind

/-- Produces a string representation. -/
@[extern "sortKind_toString"]
protected opaque toString : SortKind → String

instance : ToString SortKind := ⟨SortKind.toString⟩

/-- Produces a hash. -/
@[extern "sortKind_hash"]
protected opaque hash : SortKind → UInt64

instance : Hashable SortKind := ⟨SortKind.hash⟩

end SortKind

namespace ProofRule

/-- Produces a string representation. -/
@[extern "proofRule_toString"]
protected opaque toString : ProofRule → String

instance : ToString ProofRule := ⟨ProofRule.toString⟩

/-- Produces a hash. -/
@[extern "proofRule_hash"]
protected opaque hash : ProofRule → UInt64

instance : Hashable ProofRule := ⟨ProofRule.hash⟩

end ProofRule

namespace SkolemId

/-- Produces a string representation. -/
@[extern "skolemId_toString"]
protected opaque toString : SkolemId → String

instance : ToString SkolemId := ⟨SkolemId.toString⟩

/-- Produces a hash. -/
@[extern "skolemId_hash"]
protected opaque hash : SkolemId → UInt64

instance : Hashable SkolemId := ⟨SkolemId.hash⟩

end SkolemId

namespace ProofRewriteRule

/-- Produces a string representation. -/
@[extern "proofRewriteRule_toString"]
protected opaque toString : ProofRewriteRule → String

instance : ToString ProofRewriteRule := ⟨ProofRewriteRule.toString⟩

/-- Produces a hash. -/
@[extern "proofRewriteRule_hash"]
protected opaque hash : ProofRewriteRule → UInt64

instance : Hashable ProofRewriteRule := ⟨ProofRewriteRule.hash⟩

end ProofRewriteRule

namespace UnknownExplanation

/-- Produces a string representation. -/
@[extern "unknownExplanation_toString"]
protected opaque toString : UnknownExplanation → String

instance : ToString UnknownExplanation := ⟨UnknownExplanation.toString⟩

/-- Produces a hash. -/
@[extern "unknownExplanation_hash"]
protected opaque hash : UnknownExplanation → UInt64

instance : Hashable UnknownExplanation := ⟨UnknownExplanation.hash⟩

end UnknownExplanation

namespace RoundingMode

/-- Produces a string representation. -/
@[extern "roundingMode_toString"]
protected opaque toString : RoundingMode → String

instance : ToString RoundingMode := ⟨RoundingMode.toString⟩

/-- Produces a hash. -/
@[extern "roundingMode_hash"]
protected opaque hash : RoundingMode → UInt64

instance : Hashable RoundingMode := ⟨RoundingMode.hash⟩

end RoundingMode

namespace BlockModelsMode

/-- Produces a string representation. -/
@[extern "blockModelsMode_toString"]
protected opaque toString : BlockModelsMode → String

instance : ToString BlockModelsMode := ⟨BlockModelsMode.toString⟩

/-- Produces a hash. -/
@[extern "blockModelsMode_hash"]
protected opaque hash : BlockModelsMode → UInt64

instance : Hashable BlockModelsMode := ⟨BlockModelsMode.hash⟩

end BlockModelsMode

namespace LearnedLitType

/-- Produces a string representation. -/
@[extern "learnedLitType_toString"]
protected opaque toString : LearnedLitType → String

instance : ToString LearnedLitType := ⟨LearnedLitType.toString⟩

/-- Produces a hash. -/
@[extern "learnedLitType_hash"]
protected opaque hash : LearnedLitType → UInt64

instance : Hashable LearnedLitType := ⟨LearnedLitType.hash⟩

end LearnedLitType

namespace ProofComponent

/-- Produces a string representation. -/
@[extern "proofComponent_toString"]
protected opaque toString : ProofComponent → String

instance : ToString ProofComponent := ⟨ProofComponent.toString⟩

/-- Produces a hash. -/
@[extern "proofComponent_hash"]
protected opaque hash : ProofComponent → UInt64

instance : Hashable ProofComponent := ⟨ProofComponent.hash⟩

end ProofComponent

namespace ProofFormat

/-- Produces a string representation. -/
@[extern "proofFormat_toString"]
protected opaque toString : ProofFormat → String

instance : ToString ProofFormat := ⟨ProofFormat.toString⟩

/-- Produces a hash. -/
@[extern "proofFormat_hash"]
protected opaque hash : ProofFormat → UInt64

instance : Hashable ProofFormat := ⟨ProofFormat.hash⟩

end ProofFormat

namespace FindSynthTarget

/-- Produces a string representation. -/
@[extern "findSynthTarget_toString"]
protected opaque toString : FindSynthTarget → String

instance : ToString FindSynthTarget := ⟨FindSynthTarget.toString⟩

/-- Produces a hash. -/
@[extern "findSynthTarget_hash"]
protected opaque hash : FindSynthTarget → UInt64

instance : Hashable FindSynthTarget := ⟨FindSynthTarget.hash⟩

end FindSynthTarget

namespace InputLanguage

/-- Produces a string representation. -/
@[extern "inputLanguage_toString"]
protected opaque toString : InputLanguage → String

instance : ToString InputLanguage := ⟨InputLanguage.toString⟩

/-- Produces a hash. -/
@[extern "inputLanguage_hash"]
protected opaque hash : InputLanguage → UInt64

instance : Hashable InputLanguage := ⟨InputLanguage.hash⟩

end InputLanguage

private opaque ResultImpl : NonemptyType.{0}

/-- Encapsulation of a three-valued solver result, with explanations. -/
def Result : Type := ResultImpl.type

instance Result.instNonemptyResult : Nonempty Result := ResultImpl.property

private opaque SynthResultImpl : NonemptyType.{0}

/-- Encapsulation of a three-valued solver result, with explanations. -/
def SynthResult : Type := SynthResultImpl.type

instance SynthResult.instNonemptySynthResult : Nonempty SynthResult := SynthResultImpl.property

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

/-- Error type. -/
inductive Error where
  | missingValue
  | error (msg : String)
  | recoverable (msg : String)
  | unsupported (msg : String)
  | option (msg : String)
deriving Repr

/-- Cvc5 environment monad transformer.

Most monadic functions in this API use the non-transformer monad `cvc5.Env`, where `m := BaseIO`.

When using an `EnvT m α`, do make sure `m` is such that `MonadLiftT BaseIO m` which gives
`MonadLiftT Env (EnvT m)`.
-/
abbrev EnvT (m : Type → Type) (α : Type) : Type :=
  ExceptT Error m α

/-- Cvc5 environment monad in `BaseIO`. -/
abbrev Env (α : Type) := EnvT BaseIO α

namespace EnvT

-- functions used by the underlying C++ layer
section ffi variable [Monad m]

@[export env_pure]
private def env_pure (a : α) : Env α := return a

@[export env_bool]
private def env_bool (b : Bool) : Env Bool := return b

@[export env_uint64]
private def env_uint64 (u : UInt64) : Env UInt64 := return u

@[export env_throw]
private def env_throw (e : Error) : Env α := throw e

@[export env_throw_string]
private def env_throw_string (e : String) : Env α := throw <| (.error e)

end ffi

end EnvT

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

private opaque TermManagerImpl : NonemptyType.{0}

/-- Manager for cvc5 terms. -/
def TermManager : Type := TermManagerImpl.type

namespace TermManager

instance : Nonempty TermManager := TermManagerImpl.property

/-- Constructor. -/
extern_def new : Env TermManager

end TermManager

private opaque SolverImpl : NonemptyType.{0}

/-- A cvc5 solver. -/
def Solver : Type := SolverImpl.type

namespace Solver

instance : Nonempty Solver := SolverImpl.property

/-- Constructor.

- `tm` The associated term manager instance.
-/
extern_def new : (tm : TermManager) → Env Solver

end Solver

private opaque DatatypeConstructorDeclImpl : NonemptyType.{0}

/-- A cvc5 datatype constructor declaration.

A datatype constructor declaration is a specification used for creating a datatype constructor.
-/
def DatatypeConstructorDecl : Type := DatatypeConstructorDeclImpl.type

namespace DatatypeConstructorDecl

instance : Nonempty DatatypeConstructorDecl := DatatypeConstructorDeclImpl.property

/-- A string representation of this datatype constructor declaration. -/
protected extern_def toString : DatatypeConstructorDecl → String

instance : ToString DatatypeConstructorDecl := ⟨DatatypeConstructorDecl.toString⟩

end DatatypeConstructorDecl

private opaque DatatypeDeclImpl : NonemptyType.{0}

/-- A cvc5 datatype declaration.

A datatype declaration is not itself a datatype (see `Datatype`), but a specification for creating a
datatype sort.

The interface for a datatype declaration coincides with the syntax for the SMT-LIB 2.6 command
`declare-datatype`, or a single datatype within the `declare-datatypes` command.

`Datatype` sorts can be constructed from a `DatatypeDecl` using:
- `Solver.mkDatatypeSort`
- `Solver.mkDatatypeSorts`
-/
def DatatypeDecl : Type := DatatypeDeclImpl.type

namespace DatatypeDecl

instance : Nonempty DatatypeDecl := DatatypeDeclImpl.property

/-- Get a string representation of this datatype declaration. -/
protected extern_def toString : DatatypeDecl → String

instance : ToString DatatypeDecl := ⟨DatatypeDecl.toString⟩

end DatatypeDecl

private opaque DatatypeSelectorImpl : NonemptyType.{0}

/-- A cvc5 datatype selector. -/
def DatatypeSelector : Type := DatatypeSelectorImpl.type

namespace DatatypeSelector

instance : Nonempty DatatypeSelector := DatatypeSelectorImpl.property

/-- Gte the string representation of this datatype selector. -/
protected extern_def toString : DatatypeSelector → String

instance : ToString DatatypeSelector := ⟨DatatypeSelector.toString⟩

end DatatypeSelector

private opaque DatatypeConstructorImpl : NonemptyType.{0}

/-- A cvc5 datatype constructor. -/
def DatatypeConstructor : Type := DatatypeConstructorImpl.type

namespace DatatypeConstructor

instance : Nonempty DatatypeConstructor := DatatypeConstructorImpl.property

/-- A string representation of this datatype. -/
protected extern_def toString : DatatypeConstructor → String

instance : ToString DatatypeConstructor := ⟨DatatypeConstructor.toString⟩

end DatatypeConstructor

private opaque DatatypeImpl : NonemptyType.{0}

/-- A cvc5 datatype. -/
def Datatype : Type := DatatypeImpl.type

namespace Datatype

instance : Nonempty Datatype := DatatypeImpl.property

/-- A string representation of this datatype. -/
protected extern_def toString : Datatype → String

instance : ToString Datatype := ⟨Datatype.toString⟩

end Datatype

private opaque GrammarImpl : NonemptyType.{0}

/-- A Sygus Grammar.

This class can be used to define a context-free grammar of terms. Its interface coincides with the
definition of grammars in the SyGuS IF 2.1 standard.
-/
def Grammar : Type := GrammarImpl.type

namespace Grammar

instance : Nonempty Grammar := GrammarImpl.property

/-- A string representation of this grammar. -/
protected extern_def toString : Grammar → String

instance : ToString Grammar := ⟨Grammar.toString⟩

end Grammar

private opaque CommandImpl : NonemptyType.{0}

/-- Encapsulation of a command.

Commands are constructed by the `InputParser` and can be invoked on the `Solver` and
`Command`.
-/
def Command : Type := CommandImpl.type

namespace Command

instance : Nonempty Command := CommandImpl.property

/-- Get a string representation of this command. -/
protected extern_def toString : Command → String

instance : ToString Command := ⟨Command.toString⟩

end Command

private opaque SymbolManagerImpl : NonemptyType.{0}

/-- Symbol manager.

Internally, this class manages a symbol table and other meta-information pertaining to SMT2 file
inputs (*e.g.* named assertions, declared functions, *etc.*).

A symbol manager can be modified by invoking commands, see `Command.invoke`.

A symbol manager can be provided when constructing an `InputParser`, in which case that
`InputParser` has symbols of this symbol manager preloaded.

The symbol manager's interface is otherwise not publicly available.
-/
def SymbolManager : Type := SymbolManagerImpl.type

namespace SymbolManager

instance SymbolManager.instNonempty : Nonempty SymbolManager := SymbolManagerImpl.property

/-- Constructor.

- `tm` The associated term manager instance.
-/
extern_def new : (tm : TermManager) → Env SymbolManager

end SymbolManager

private opaque InputParserImpl : NonemptyType.{0}

/-- This type is the main interface for retrieving commands and expressions from an input using a
  parser.

After construction, it is expected that an input is first configured via, e.g.,
`InputParser.setFileInput`, `InputParser.setStreamInput`, `InputParser.setStringInput` or
`InputParser.setIncrementalStringInput` and `InputParser.appendIncrementalStringInput`. Then,
functions `InputParser.nextCommand` and `InputParser.nextExpression` can be invoked to parse the
input.

The input parser interacts with a symbol manager, which determines which symbols are defined in the
current context, based on the background logic and user-defined symbols. If no symbol manager is
provided, then the input parser will construct (an initially empty) one.

If provided, the symbol manager must have a logic that is compatible with the provided solver. That
is, if both the solver and symbol manager have their logics set (`SymbolManager.isLogicSet` and
`Solver.isLogicSet`), then their logics must be the same.

Upon setting an input source, if either the solver (resp. symbol manager) has its logic set, then
the symbol manager (resp. solver) is set to use that logic, if its logic is not already set.
-/
def InputParser : Type := InputParserImpl.type

namespace InputParser

instance : Nonempty InputParser := InputParserImpl.property

/-- Construct an input parser with an initially empty symbol manager.

- `solver`: The solver (e.g. for constructing terms and sorts).
-/
private extern_def ofSolver : (solver : Solver) → Env InputParser

/-- Construct an input parser.

- `solver` The solver (e.g. for constructing terms and sorts).
- `sm` The symbol manager, which contains a symbol table that maps symbols to terms and sorts. Must
  have a logic that is compatible with the solver.
-/
private extern_def ofSolverAndSM : (solver : Solver) → (sm : SymbolManager) → Env InputParser

@[inherit_doc ofSolverAndSM]
def new (solver : Solver) : (sm : Option SymbolManager := none) → Env InputParser
  | none => ofSolver solver
  | some sm => ofSolverAndSM solver sm

end InputParser

namespace Result

/-- Comparison for structural equality. -/
protected extern_def beq : Result → Result → Bool

instance : BEq Result := ⟨Result.beq⟩

/-- Hash function for cvc5 sorts. -/
protected extern_def hash : Result → UInt64

instance : Hashable Result := ⟨Result.hash⟩

/-- True if this result is from a satisfiable `checkSat` or `checkSatAssuming` query. -/
extern_def isSat : Result → Bool

/-- True if this result is from a unsatisfiable `checkSat` or `checkSatAssuming` query. -/
extern_def isUnsat : Result → Bool

/-- True if this result is from a `checkSat` or `checkSatAssuming` query and cvc5 was not able to
determine (un)satisfiability.
-/
extern_def isUnknown : Result → Bool

/-- An explanation for an unknown query result.

Note that if the result is (un)sat, this function returns `UnknownExplanation.UNKNOWN_REASON`.
-/
extern_def getUnknownExplanation : Result → UnknownExplanation
with
  /-- An explanation for an unknown query result, `none` if the result in not unknown. -/
  getUnknownExplanation? (res : Result) : Option UnknownExplanation :=
    if ¬ res.isUnknown then none else res.getUnknownExplanation

/-- A string representation of this result. -/
protected extern_def toString : Result → String

instance : ToString Result := ⟨Result.toString⟩

end Result

namespace SynthResult

/-- A string representation of this synthesis result. -/
protected extern_def toString : SynthResult → String

instance : ToString SynthResult := ⟨SynthResult.toString⟩

/-- Hash function for synthesis results. -/
protected extern_def hash : SynthResult → UInt64

instance : Hashable SynthResult := ⟨SynthResult.hash⟩

/-- Equality of two synthesis results. -/
protected extern_def beq : SynthResult → SynthResult → Bool

instance : BEq SynthResult := ⟨SynthResult.beq⟩

/-- Determine if a given synthesis result is empty (a nullary result) and not an actual result
  returned from a synthesis query.
-/
extern_def isNull : SynthResult → Bool

/-- True if the synthesis query has a solution. -/
extern_def hasSolution : SynthResult → Bool

/-- True if the synthesis query has no solution. In this case, it was determined that there was no
  solution.
-/
extern_def hasNoSolution : SynthResult → Bool

/-- True if the result of the synthesis query could not be determined. -/
extern_def isUnknown : SynthResult → Bool

end SynthResult

section ffi_except_constructors

/-- Only used by FFI to inject values. -/
@[export generic_except_ok]
private def mkExceptOk {α : Type} : α → Except Error α := .ok

/-- Only used by FFI to inject values. -/
@[export except_ok_bool]
private def mkExceptOkBool : Bool → Except Error Bool := .ok

/-- Only used by FFI to inject values. -/
@[export except_ok_i64]
private def mkExceptOkI64 : Int64 → Except Error Int64 := .ok

/-- Only used by FFI to inject values. -/
@[export except_ok_u64]
private def mkExceptOkU64 : Int64 → Except Error Int64 := .ok

/-- Only used by FFI to inject values. -/
@[export except_ok_u32]
private def mkExceptOkU32 : UInt32 → Except Error UInt32 := .ok

/-- Only used by FFI to inject values. -/
@[export except_ok_i32]
private def mkExceptOkI32 : Int32 → Except Error Int32 := .ok

/-- Only used by FFI to inject values. -/
@[export except_ok_u16]
private def mkExceptOkU16 : UInt16 → Except Error UInt16 := .ok

/-- Only used by FFI to inject values. -/
@[export except_ok_u8]
private def mkExceptOkU8 : UInt8 → Except Error UInt8 := .ok

/-- Only used by FFI to inject errors. -/
@[export generic_except_err]
private def mkExceptErr {α : Type} : Error → Except Error α := .error

/-- Only used by FFI to inject errors. -/
@[export generic_except_err_of_string]
private def mkExceptErrOfString {α : Type} : String → Except Error α := .error ∘ Error.error

end ffi_except_constructors

namespace DatatypeConstructorDecl

/-- The null datatype constructor declaration. -/
extern_def null : Unit → DatatypeConstructorDecl

/-- True if this `DatatypeConstructorDecl` is a null declaration. -/
extern_def isNull : DatatypeConstructorDecl → Bool

/-- Equality operator. -/
protected extern_def beq : DatatypeConstructorDecl → DatatypeConstructorDecl → Bool

instance : BEq DatatypeConstructorDecl := ⟨DatatypeConstructorDecl.beq⟩

/-- Hash function for datatype declarations. -/
protected extern_def hash : DatatypeConstructorDecl → UInt64

instance : Hashable DatatypeConstructorDecl := ⟨DatatypeConstructorDecl.hash⟩

/-- Add datatype selector declaration.

- `name` The name of the datatype selector declaration to add.
- `sort` The codomain sort of the datatype selector declaration to add.
-/
extern_def addSelector :
  (dtCons : DatatypeConstructorDecl) → (name : String) → (sort : cvc5.Sort) →
  Env DatatypeConstructorDecl

/-- Add datatype selector declaration whose codomain type is the datatype itself.

- `name` The name of the datatype selector declaration to add.
-/
extern_def addSelectorSelf :
  (dtCons : DatatypeConstructorDecl) → (name : String) → Env DatatypeConstructorDecl

/-- Add datatype selector declaration whose codomain sort is an unresolved datatype with the given
  name.

- `name` The name of the datatype selector declaration to add.
- `unresDatatypeName` The name of the unresolved datatype. The codomain of the selector will be the
  resolved datatype with the given name
-/
extern_def addSelectorUnresolved :
  (dtCons : DatatypeConstructorDecl) → (name : String) → (unresDatatypeName : String) →
  Env DatatypeConstructorDecl

end DatatypeConstructorDecl

namespace DatatypeDecl

/-- The null datatype declaration. -/
extern_def null : Unit → DatatypeDecl

instance : Inhabited DatatypeDecl := ⟨null ()⟩

/-- Determine if this datatype declaration is nullary. -/
extern_def isNull : DatatypeDecl → Bool

/-- Equality operator. -/
protected extern_def beq : DatatypeDecl → DatatypeDecl → Bool

instance : BEq DatatypeDecl := ⟨DatatypeDecl.beq⟩

/-- Hash function for datatype declarations. -/
protected extern_def hash : DatatypeDecl → UInt64

instance : Hashable DatatypeDecl := ⟨DatatypeDecl.hash⟩

/-- Add datatype constructor declaration.

- `ctor` The datatype constructor declaration to add.
-/
extern_def addConstructor :
  DatatypeDecl → (ctor : DatatypeConstructorDecl) → Env DatatypeDecl

/-- Get the number of constructors for this datatype declaration. -/
extern_def getNumConstructors : DatatypeDecl → Nat

/-- Determine if this datatype declaration is parametric.

**Warning**: this function is experimental and may change in future versions.
-/
extern_def isParametric : DatatypeDecl → Bool

/-- Get the name of this datatype declaration. -/
extern_def!? getName : DatatypeDecl → Except Error String

/-- Determine if this datatype declaration is resolved (has already been used to declare a
datatype).
-/
extern_def isResolved : DatatypeDecl → Env Bool

end DatatypeDecl

namespace DatatypeSelector

/-- The null datatype constructor. -/
extern_def null : Unit → DatatypeSelector

instance : Inhabited DatatypeSelector := ⟨null ()⟩

/-- True if this datatype is a null object. -/
extern_def isNull : DatatypeSelector → Bool

/-- Equality operator. -/
protected extern_def beq : DatatypeSelector → DatatypeSelector → Bool

instance : BEq DatatypeSelector := ⟨DatatypeSelector.beq⟩

/-- Hash function for datatype selectors. -/
protected extern_def hash : DatatypeSelector → UInt64

instance : Hashable DatatypeSelector := ⟨DatatypeSelector.hash⟩

/-- Get the name of this datatype selector. -/
extern_def!? getName : DatatypeSelector → Except Error String

/-- Get the selector term of this datatype selector.

Selector terms are a class of function-like terms of selector sort (`Sort.isDatatypeSelector`), and
should be used as the first argument of terms of kind `Kind.APPLY_SELECTOR`.
-/
extern_def getTerm : DatatypeSelector → Env Term

/-- Get the updater term of this datatype selector.

Similar to selectors, updater terms are a class of function-like terms of updater sort
(`Sort.isDatatypeUpdater`), and should be used as the first argument of terms of kind
`Kind.APPLY_UPDATER`.
-/
extern_def getUpdaterTerm : DatatypeSelector → Env Term

/-- Get the codomain sort of this selector. -/
extern_def getCodomainSort : DatatypeSelector → Env cvc5.Sort

end DatatypeSelector

namespace DatatypeConstructor

/-- The null datatype constructor. -/
extern_def null : Unit → DatatypeConstructor

instance : Inhabited DatatypeConstructor := ⟨null ()⟩

/-- True if this datatype is a null object. -/
extern_def isNull : DatatypeConstructor → Bool

/-- Equality operator. -/
protected extern_def beq : DatatypeConstructor → DatatypeConstructor → Bool

instance : BEq DatatypeConstructor := ⟨DatatypeConstructor.beq⟩

/-- Hash function for datatype constructors. -/
protected extern_def hash : DatatypeConstructor → UInt64

instance : Hashable DatatypeConstructor := ⟨DatatypeConstructor.hash⟩

/-- Get the name of this datatype constructor. -/
extern_def!? getName : DatatypeConstructor → Except Error String

/-- Get the constructor term of this datatype constructor.

Datatype constructors are a special class of function-like terms whose sort is datatype constructor
(`Sort.isDatatypeConstructor`). All datatype constructors, including nullary ones, should be used as
the first argument to terms whose kind is `Kind.APPLY_CONSTRUCTOR`. For example, the nil list can
be constructor by `tm.mkTerm Kind.APPLY_CONSTRUCTOR #[t]`, where `tm` is a `TermManager` and `t` is
the term returned by this function.

This function should not be used for parametric datatypes. Instead, use the function
`DatatypeConstructor.getInstantiatedTerm`.
-/
extern_def getTerm : DatatypeConstructor → Env Term

/-- Get the constructor term of this datatype constructor whose return type is `retSort`.

This function is intended to be used on constructors of parametric datatypes and can be seen as
returning the constructor term that has been explicitly cast to the given sort.

This function is required for constructors of parametric datatypes whose return type cannot be
determined by type inference. For example, given:

```smtlib
(declare-datatype List (par (T) ((nil) (cons (head T) (tail (List T))))))
```

The type of nil terms must be provided by the user. In SMT version 2.6, this is done via the syntax
for qualified identifiers:

```smtlib
(as nil (List Int))
```

This function is equivalent of applying the above, where this DatatypeConstructor is the one
corresponding to `nil`, and `retSort` is `(List Int)`.

The returned constructor term `t` is used to construct the above (nullary) application of `nil` with
`TermManager::mkTerm(Kind::APPLY_CONSTRUCTOR, {t})`.

**Warning**: this function is experimental and may change in future versions.

- `retSort` The desired return sort of the constructor.
-/
extern_def getInstantiatedTerm : DatatypeConstructor → (retSort : cvc5.Sort) → Env Term

/-- Get the tester term of this datatype constructor.

Similar to constructors, testers are a class of function-like terms of tester sort
(`Sort.isDatatypeTester`) which should be used as the first argument of terms of kind
`Kind.APPLY_TESTER`.
-/
extern_def getTesterTerm : DatatypeConstructor → Env Term

/-- The number of selectors of this datatype constructor. -/
extern_def getNumSelectors : DatatypeConstructor → Nat

/-- Get the datatype selector with the given name.

This is a linear search through the selectors, so in case of multiple, similarly-named selectors,
the first is returned.

- `name` The name of the datatype selector.
-/
extern_def getSelector : DatatypeConstructor → (name : String) → Env DatatypeSelector

/-- The datatype selector at index `idx`. -/
extern_def getSelectorAt :
  (dtCons : DatatypeConstructor) → (idx : Fin dtCons.getNumSelectors) → DatatypeSelector

instance : GetElem DatatypeConstructor Nat DatatypeSelector
  fun dt idx => idx < dt.getNumSelectors
where
  getElem dt idx h := dt.getSelectorAt ⟨idx, h⟩

instance [Monad m] : ForIn m DatatypeConstructor DatatypeSelector where
  forIn dtCons init fold := forIn' [:dtCons.getNumSelectors] init fun idx h_member acc =>
    let selector := dtCons.getSelectorAt ⟨idx, h_member.upper⟩
    fold selector acc

end DatatypeConstructor

namespace Datatype

/-- The null datatype. -/
extern_def null : Unit → Datatype

instance : Inhabited Datatype := ⟨null ()⟩

/-- True if this datatype is a null object. -/
extern_def isNull : Datatype → Bool

/-- Equality operator. -/
protected extern_def beq : Datatype → Datatype → Bool

instance : BEq Datatype := ⟨Datatype.beq⟩

/-- Hash function for datatypes. -/
protected extern_def hash : Datatype → UInt64

instance : Hashable Datatype := ⟨Datatype.hash⟩

/-- Get the datatype constructor with the given name.

This is a linear search through the constructors, so in case of multiple, similarly-named
constructors, the first is returned.

- `name` The name of the datatype constructor.
-/
extern_def getConstructor : Datatype → (name : String) → Env DatatypeConstructor

/-- Get the number of constructors of this datatype. -/
extern_def getNumConstructors : Datatype → Nat

/-- Get the datatype constructor at a given index.

- `idx` The index of the datatype constructor to return.
-/
extern_def getConstructorAt :
  (dt : Datatype) → (idx : Fin dt.getNumConstructors) → DatatypeConstructor

instance : GetElem Datatype Nat DatatypeConstructor
  fun dt idx => idx < dt.getNumConstructors
where
  getElem dt idx h := dt.getConstructorAt ⟨idx, h⟩

instance [Monad m] : ForIn m Datatype DatatypeConstructor where
  forIn dt init fold := forIn' [:dt.getNumConstructors] init fun idx h_member acc =>
    let constructor := dt.getConstructorAt ⟨idx, h_member.upper⟩
    fold constructor acc

/-- Get the datatype selector with the given name.

This is a linear search through the constructors and their selectors, so in case of multiple,
similarly-named selectors, the first is returned.

- `name` The name of the datatype selector.
-/
extern_def getSelector : Datatype → (name : String) → Env DatatypeSelector

/-- Get the name of this datatype. -/
extern_def!? getName : Datatype → Except Error String

/-- Get the parameters of this datatype, if it is parametric.

Asserts that this datatype is parametric.

**Warning**: this function is experimental and may change in future versions.
-/
extern_def getParameters : Datatype → Env (Array cvc5.Sort)

/-- Determine if this datatype is parametric.

**Warning**: this function is experimental and may change in future versions.
-/
extern_def isParametric : Datatype → Bool

/-- Determine if this datatype corresponds to a co-datatype. -/
extern_def isCodatatype : Datatype → Bool

/-- Determine if this datatype corresponds to a tuple. -/
extern_def isTuple : Datatype → Bool

/-- Determine if this datatype corresponds to a record.

**Warning**: this function is experimental and may change in future versions.
-/
extern_def isRecord : Datatype → Bool

/-- Determine if this datatype is finite. -/
extern_def isFinite : Datatype → Except Error Bool

/-- Determine if this datatype is well-founded.

If this datatype is not a codatatype, this returns false if thre are no values of this datatype
that are of finite size.
-/
extern_def isWellFounded : Datatype → Bool

end Datatype

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
extern_def!? getKind : cvc5.Sort → Except Error SortKind

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

instance : ToString cvc5.Sort := ⟨Sort.toString⟩
instance : Repr cvc5.Sort := ⟨fun self _ => self.toString⟩

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

/-- Get the underlying datatype of a datatype sort. -/
extern_def!? getDatatype : cvc5.Sort → Except Error Datatype

/-- Get the sorts used to instantiate the sort parameters of a parametric sort.

A parametric sort is a parametric datatype or an uninterpreted sort constructor sort.
See `cvc5.Sort.instantiate`. -/
extern_def!? getInstantiatedParameters : cvc5.Sort → Except Error (Array cvc5.Sort)

/-- Instantiate a parameterized datatype sort or uninterpreted sort constructor sort.

Create sort parameters with `mkParamSort symbol`.

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
extern_def!? substitute :
  cvc5.Sort → (sorts : Array cvc5.Sort) → (replacements : Array cvc5.Sort) → Except Error cvc5.Sort

/-- The arity of a datatype constructor sort. -/
extern_def!? getDatatypeConstructorArity : cvc5.Sort → Except Error Nat

/-- The domain sorts of a datatype constructor sort. -/
extern_def!? getDatatypeConstructorDomainSorts : cvc5.Sort → Except Error (Array cvc5.Sort)

/-- The codomain sort of a constructor sort. -/
extern_def!? getDatatypeConstructorCodomainSort : cvc5.Sort → Except Error cvc5.Sort

/-- The domain sort of a datatype selector sort. -/
extern_def!? getDatatypeSelectorDomainSort : cvc5.Sort → Except Error cvc5.Sort

/-- The codomain sort of a datatype selector sort. -/
extern_def!? getDatatypeSelectorCodomainSort : cvc5.Sort → Except Error cvc5.Sort

/-- The domain sort of a datatype tester sort. -/
extern_def!? getDatatypeTesterDomainSort : cvc5.Sort → Except Error cvc5.Sort

/-- The codomain sort of a datatype tester sort. -/
extern_def!? getDatatypeTesterCodomainSort : cvc5.Sort → Except Error cvc5.Sort

/-- Get the arity of a datatype sort.

Number of type parameters if the datatype is parametric, `0` otherwise.
-/
extern_def!? getDatatypeArity : cvc5.Sort → Except Error Nat

end cvc5.Sort

namespace cvc5

namespace Op

/-- The null operator. -/
extern_def null : Unit → Op

instance : Inhabited Op := ⟨null ()⟩

/-- Hash function. -/
protected extern_def hash : Op → UInt64

instance : Hashable Op := ⟨Op.hash⟩

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

/-- Less than comparison. -/
protected extern_def blt : Term → Term → Bool

/-- Greater than comparison. -/
protected extern_def bgt : Term → Term → Bool

/-- Less than or equal comparison. -/
protected extern_def ble : Term → Term → Bool

/-- Greater than or equal comparison. -/
protected extern_def bge : Term → Term → Bool

/-- Comparison of two terms. -/
protected def compare (t1 t2 : cvc5.Term) : Ordering :=
  if t1.beq t2 then .eq else if t1.bgt t2 then .gt else .lt

instance : Ord Term := ⟨Term.compare⟩

instance : LT Term := ⟨(Term.blt · ·)⟩

instance : DecidableLT Term :=
  fun t1 t2 => if h : t1.blt t2 then .isTrue h else .isFalse h

instance : LE Term := ⟨(Term.ble · ·)⟩

instance : DecidableLE Term :=
  fun t1 t2 => if h : t1.ble t2 then .isTrue h else .isFalse h

/-- Hash function for terms. -/
protected extern_def hash : Term → UInt64

instance : Hashable Term := ⟨Term.hash⟩

/-- Determine if this term is nullary. -/
extern_def isNull : Term → Bool

/-- Get the kind of this term. -/
extern_def!? getKind : Term → Except Error Kind

/-- Get the sort of this term. -/
extern_def!? getSort : Term → Except Error cvc5.Sort

/-- Simultaneously replace `terms` with `replacements` in `term`.

- `terms`: The terms to replace.
- `replacements`: The replacement terms.

In the case that `terms` contains duplicates, the replacement earliest in the array takes priority.
For example, calling `substitute` on `f(x, y)` with
- `terms := #[x, z]`
- `replacements := #[g(z), w]`
results in the term `f(g(z), y)`.

**NB:** requires that `terms` and `replacements` are of equal size (they are interpreted as a 1:1
mapping).

**NB:** this replacement is applied during a pre-order traversal and only once (it is not run until
fixed point).
-/
extern_def substitute :
  (term : Term) → (terms : Array Term) → (replacements : Array Term) → Env Term

/-- Determine if this term has an operator. -/
extern_def hasOp : Term → Bool

/-- Determine if this term has a symbol (a name).

For example, free constants and variables have symbols.
-/
extern_def!? hasSymbol : Term → Except Error Bool

/-- Get the id of this term. -/
extern_def!? getId : Term → Except Error Nat

/-- Get the number of children of this term. -/
private extern_def getNumChildrenInternal : Term → Nat
with getNumChildren (t : Term) : Nat :=
  if t.isNull then 0 else t.getNumChildrenInternal

/-- Is this term a skolem? -/
extern_def isSkolem : Term → Bool

/-- Get the child term of this term at a given index. -/
protected extern_def get : (t : Term) → Fin t.getNumChildren → Term

/-- Get the operator of a term with an operator.

Requires that this term has an operator (see `hasOp`).
-/
extern_def!? getOp : Term → Except Error Op

/-- Get the symbol of this term.

Requires that this term has a symbol (see `hasSymbol`).

The symbol of the term is the string that was provided when constructing it *via* `mkConst` or
`mkVar`.
-/
extern_def!? getSymbol : Term → Except Error String

/-- Boolean negation. -/
extern_def notTerm : Term → Env Term

/-- Boolean and.

- `t1`: A Boolean term.
- `t2`: A Boolean term.
-/
extern_def andTerm : (t1 t2 : Term) → Env Term

/-- Boolean or.

- `t1`: A Boolean term.
- `t2`: A Boolean term.
-/
extern_def orTerm : (t1 t2 : Term) → Env Term

/-- Boolean exclusive or.

- `t1`: A Boolean term.
- `t2`: A Boolean term.
-/
extern_def xorTerm : (t1 t2 : Term) → Env Term

/-- Equality. -/
extern_def eqTerm : (t1 t2 : Term) → Env Term

/-- Boolean implication.

- `t1`: A Boolean term.
- `t2`: A Boolean term.
-/
extern_def impTerm : (t1 t2 : Term) → Env Term

/-- If-then-else.

- `cnd`: The condition, a Boolean term.
- `thn`: The *then* term.
- `els`: The *else* term.
-/
extern_def iteTerm : (cnd thn els : Term) → Env Term

/-- Get the sign of an integer or real value.

Returns `0` this term is zero, `-1` if this term is a negative real or integer value, `1` if this
term is a positive real or integer value.

**NB:** requires that this term is an integer or real value.
-/
extern_def!? getRealOrIntegerValueSign : Term → Except Error Int

/-- Determine if this term is an `Int32 value`.

**NB:** this will return true for integer constants and real constants that have integer value.
-/
extern_def isInt32Value : Term → Bool

/-- Get the `Int32` representation of this integral value.

**NB:** requires that this term is an `Int32` value (see `isInt32Value`).
-/
extern_def!? getInt32Value : Term → Except Error Int32

/-- Determine if this term is an `UInt32 value`.

**NB:** this will return true for integer constants and real constants that have integer value.
-/
extern_def isUInt32Value : Term → Bool

/-- Get the `UInt32` representation of this integral value.

**NB:** requires that this term is an `UInt32` value (see `isUInt32Value`).
-/
extern_def!? getUInt32Value : Term → Except Error UInt32

/-- Determine if this term is an `Int64 value`.

**NB:** this will return true for integer constants and real constants that have integer value.
-/
extern_def isInt64Value : Term → Bool

/-- Get the `Int64` representation of this integral value.

**NB:** requires that this term is an `Int64` value (see `isInt64Value`).
-/
extern_def!? getInt64Value : Term → Except Error Int64

/-- Determine if this term is an `UInt64 value`.

**NB:** this will return true for integer constants and real constants that have integer value.
-/
extern_def isUInt64Value : Term → Bool

/-- Get the `UInt64` representation of this integral value.

**NB:** requires that this term is an `UInt64` value (see `isUInt64Value`).
-/
extern_def!? getUInt64Value : Term → Except Error UInt64

/-- Determine if this real/integer constant term is an integral value. -/
extern_def isIntegerValue : Term → Bool

/-- Get the native integral value of an integral value. -/
extern_def!? getIntegerValue : Term → Except Error Int

/-- Get the native integral value of an integral value. -/
extern_def isStringValue : Term → Bool

/-- Determine if this term is a rational value whose numerator fits into an `Int32` value and its
denominator fits into a `UInt32` value.
-/
extern_def isReal32Value : Term → Bool

/-- Get the 32 bit integer representations of the numerator and denominator of a rational value.

**NB:** Requires that this term is a rational value and its numerator and denominator fit into 32
bit integer values (see `Term.isReal32Value`).
-/
extern_def getReal32Value : Term → Except Error (Int32 × UInt32)

/-- Determine if this term is a rational value whose numerator fits into an `Int64` value and its
denominator fits into a `UInt64` value.
-/
extern_def isReal64Value : Term → Bool

/-- Get the 64 bit integer representations of the numerator and denominator of a rational value.

**NB:** Requires that this term is a rational value and its numerator and denominator fit into 64
bit integer values (see `Term.isReal64Value`).
-/
extern_def getReal64Value : Term → Except Error (Int64 × UInt64)

/-- Determine if this term is a rational value.

**NB:** A term of kind `Kind.PI` is not considered to be a real value.
-/
extern_def isRealValue : Term → Bool

/-- Get a string representation of this rational value.

**NB:** Requires that this term is a rational value (see `Term.isRealValue`).
-/
extern_def!? getRealValue : Term → Except Error String

/-- Get the native rational value of a real, rational-compatible value. -/
extern_def!? getRationalValue : Term → Except Error Rat

/-- Determine if this term is a constant array. -/
extern_def isConstArray : Term → Bool

/-- Determine the base (element stored at all indices) of a constant array.

**NB:** requires that this term is a constant array (see `isConstArray`).
-/
extern_def!? getConstArrayBase : Term → Except Error Term

/-- Determine if this term is a Boolean value. -/
extern_def isBooleanValue : Term → Bool

/-- Get the value of a Boolean term as a native Boolean value.

Requires `term` to have sort Bool.
-/
extern_def!? getBooleanValue : Term → Except Error Bool

/-- Determine if this term is a bit-vector value. -/
extern_def isBitVectorValue : Term → Bool

/-- Get the string representation of a bit-vector value.

Requires `term` to have a bit-vector sort.

- `base`: `2` for binary, `10` for decimal, and `16` for hexadecimal.
-/
extern_def!? getBitVectorValue : Term → UInt32 → Except Error String

/-- Determine if this term is a finite field value. -/
extern_def isFiniteFieldValue : Term → Bool

/-- Get the integer representation of a finite field value (base 10).

**NB:** asserts `isFiniteFieldValue`.

**NB:** uses the integer representative of smallest absolute value.
-/
extern_def!? getFiniteFieldValue : Term → Except Error Int

/-- Determine if this term is an uninterpreted sort value. -/
extern_def isUninterpretedSortValue : Term → Bool

/-- Get a string representation of an uninterpreted sort value.

**NB:**  asserts `isUninterpretedSortValue`.
-/
extern_def!? getUninterpretedSortValue : Term → Except Error String

/-- Determine if this term is a tuple value. -/
extern_def isTupleValue : Term → Bool

/-- Get a tuple value as a vector of terms.

**NB:** asserts `isTupleValue`.
-/
extern_def!? getTupleValue : Term → Except Error (Array Term)

/-- Determine if this term is a floating-point rounding mode value. -/
extern_def isRoundingModeValue : Term → Bool

/-- Get the `RoundingMode` value of a given rounding-mode value term.

**NB:** asserts `isRoundingModeValue`.
-/
extern_def!? getRoundingModeValue : Term → Except Error RoundingMode

/-- Determine if this term is a floating-point positive zero value (`+zero`). -/
extern_def isFloatingPointPosZero : Term → Bool

/-- Determine if this term is a floating-point negative zero value (`-zero`). -/
extern_def isFloatingPointNegZero : Term → Bool

/-- Determine if this term is a floating-point positive infinity value (`+oo`). -/
extern_def isFloatingPointPosInf : Term → Bool

/-- Determine if this term is a floating-point negative infinity value (`-oo`). -/
extern_def isFloatingPointNegInf : Term → Bool

/-- Determine if this term is a floating-point NaN. -/
extern_def isFloatingPointNaN : Term → Bool

/-- Determine if this term is a floating-point value. -/
extern_def isFloatingPointValue : Term → Bool

/-- Get the representation of a floating-point value.

Returns a tuple of the floating-point value's exponent width, significand width, and a bit-vector
value term.

**NB:** asserts `isFloatingPointValue`.
-/
extern_def!? getFloatingPointValue : Term → Except Error (UInt32 × UInt32 × Term)

/-- Determine if this term is a set value.

A term is a set value if it is considered to be a (canonical) constant set value. A canonical set
value is one whole AST is:

```smtlib
(union (singleton c_1) ... (union (singleton c_{n-1}) (singleton c_n))))
```

where `c_1 ... c_n` are values ordered by id such that `c_1 > ... > c_n`.

**NB:** a universe set term (`Kind.SET_UNIVERSE`) is not considered to be a set value.
-/
extern_def isSetValue : Term → Bool

/-- Get a set value as an array of terms.

**NB:** asserts `isSetValue`.
-/
extern_def!? getSetValue : Term → Except Error (Array Term)

/-- Determine if this term is a sequence value.

A term is a sequence value if it has kind `Kind.CONST_SEQUENCE`. In contrast to values for the set
sort (as described in `isSetValue`), a sequence value is represented as a term with no children.

Semantically, a sequence value is a concatenation of unit sequences whose elements are themselves
values. For example:

```smtlib
(seq.++ (seq.unit 0) (seq.unit 1))
```

The above term has two representations in `Term`. One is as the sequence concatenation term:

```lisp
(SEQ_CONCAT (SEQ_UNIT 0) (SEQ_UNIT 1))
```

where `0` and `1` are the terms corresponding to the integer constants `0` and `1`.

Alternatively, the above term is represented as the constant sequence value:

```lisp
CONST_SEQUENCE_{0, 1}
```

where calling `getSequenceValue` on the latter returns the array `#[0, 1]`.

The former term is not a sequence value, but the latter term is.

Constant sequences cannot be constructed directly *via* the API. They are returned in response to
API calls such as `Solver.getValue` and `Solver.simplify`.
-/
extern_def isSequenceValue : Term → Bool

/-- Get a sequence value as a vector of terms. -/
extern_def!? getSequenceValue : Term → Except Error (Array Term)

/-- Determine if this term is a cardinality constraint. -/
private extern_def isCardinalityConstraintInternal : Term → Bool
with isCardinalityConstraint (t : Term) :=
  if t.isNull then false else t.isCardinalityConstraintInternal

/-- Get a cardinality constraint as a pair of its sort and upper bound.

**NB:** asserts `isCardinalityConstraint`.
-/
extern_def!? getCardinalityConstraint : Term → Except Error (cvc5.Sort × UInt32)

/-- Determine if this term is a real algebraic number. -/
extern_def isRealAlgebraicNumber : Term → Bool

/-- Get the defining polynomial for a real algebraic number term, expressed in terms of the given
variable.

**NB:** asserts `isRealAlgebraicNumber`.

- `v` The variable over which to express the polynomial.
-/
extern_def!? getRealAlgebraicNumberDefiningPolynomial : Term → (v : Term) → Except Error Term

/-- Get the lower bound for a real algebraic number value.

**NB:** asserts `isRealAlgebraicNumber`.
-/
extern_def!? getRealAlgebraicNumberLowerBound : Term → Except Error Term

/-- Get the upper bound for a real algebraic number value.

**NB:** asserts `isRealAlgebraicNumber`.
-/
extern_def!? getRealAlgebraicNumberUpperBound : Term → Except Error Term

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

instance [Monad m] : ForIn m Term Term where
  forIn := Term.forIn

/-- Get the children of a term. -/
def getChildren (t : Term) : Array Term := Id.run do
  let mut cts := #[]
  for ct in t do
    cts := cts.push ct
  cts

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

/-- Get the Boolean sort. -/
extern_def getBooleanSort : TermManager → Env cvc5.Sort

/-- Get the Integer sort. -/
extern_def getIntegerSort : TermManager → Env cvc5.Sort

/-- Get the Real sort. -/
extern_def getRealSort : TermManager → Env cvc5.Sort

/-- Get the regular expression sort. -/
extern_def getRegExpSort : TermManager → Env cvc5.Sort

/-- Get the rounding mode sort. -/
extern_def getRoundingModeSort : TermManager → Env cvc5.Sort

/-- Get the string sort. -/
extern_def getStringSort : TermManager → Env cvc5.Sort

/-- Create an array sort.

- `indexSort` The array index sort.
- `elemSort` The array element sort.
-/
extern_def mkArraySort : TermManager → (indexSort elemSort : cvc5.Sort) → Env cvc5.Sort

/-- Create a bit-vector sort.

- `size` The bit-width of the bit-vector sort.
-/
extern_def mkBitVectorSort : TermManager → (size : UInt32) → Env cvc5.Sort

/-- Create a floating-point sort.

- `exp` The bit-width of the exponent of the floating-point sort.
- `sig` The bit-width of the significand of the floating-point sort.
-/
extern_def mkFloatingPointSort : TermManager → (exp sig : UInt32) → Env cvc5.Sort

/-- Create a finite-field sort from a given string of base n.

- `size` The modulus of the field. Must be a prime.
- `base` The base of the string representation of `size`.
-/
extern_def mkFiniteFieldSortOfString :
  TermManager → (size : String) → (base : UInt32 := 10) → Env cvc5.Sort
with
  /-- Create a finite-field sort.

  - `size` The modulus of the field in base 10. Must be a prime.
  -/
  mkFiniteFieldSort (tm : TermManager) (size : Nat) : Env cvc5.Sort :=
    mkFiniteFieldSortOfString tm (toString size) (base := 10)

/-- Create function sort.

- `sorts` The sort of the function arguments.
- `codomain` The sort of the function return value.
-/
extern_def mkFunctionSort :
  TermManager → (sorts : Array cvc5.Sort) → (cod : cvc5.Sort) → Env cvc5.Sort

/-- Create a skolem.

- `id`: The skolem identifier.
- `indices`: The indices of the skolem.
-/
extern_def mkSkolem : TermManager →  (id : SkolemId) → (indices : Array Term) → Env Term

/-- Get the number of indices for a skolem id.

- `id`: The skolem id.
-/
extern_def!? getNumIndicesForSkolemId : TermManager → (id : SkolemId) → Except Error Nat

/-- Create a predicate sort.

This is equivalent to calling `mkFunctionSort` with Boolean sort as the codomain.

- `sorts` The list of sorts of the predicate.
-/
extern_def mkPredicateSort : TermManager → (sorts : Array cvc5.Sort) → Env cvc5.Sort

/-- Create a tuple sort.

- `sorts` The sorts of the elements of the tuple.
-/
extern_def mkTupleSort : TermManager → (sorts : Array cvc5.Sort) → Env cvc5.Sort

/-- Create a record sort.

**Warning**: This function is experimental and may change in future versions.

- `fields` The list of fields of the record.
-/
extern_def mkRecordSort : TermManager → (fields : Array (String × cvc5.Sort)) → Env cvc5.Sort

/-- Create an uninterpreted sort constructor sort.

An uninterpreted sort constructor is an uninterpreted sort with arity > 0.

- `arity` The arity of the sort (must be > 0).
- `symbol` The symbol of the sort.
-/
extern_def mkUninterpretedSortConstructorSort :
  TermManager → (arity : Nat) → (symbol : String := "") → Env cvc5.Sort

/-- Create a set parameter.

- `elemSort` The sort of the set elements.
-/
extern_def mkSetSort : TermManager → (sort : cvc5.Sort) → Env cvc5.Sort

/-- Create a set parameter.

- `elemSort` The sort of the set elements.
-/
extern_def mkBagSort : TermManager → (sort : cvc5.Sort) → Env cvc5.Sort

/-- Create a set parameter.

- `elemSort` The sort of the set elements.
-/
extern_def mkSequenceSort : TermManager → (sort : cvc5.Sort) → Env cvc5.Sort

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
extern_def mkAbstractSort : TermManager → (k : SortKind) → Env cvc5.Sort

/-- Create an uninterpreted sort.

- `symbol` The name of the sort.
-/
extern_def mkUninterpretedSort : TermManager → (symbol : String) → Env cvc5.Sort

/-- Create an unresolved datatype sort.

This is for creating yet unresolved sort placeholders for mutually recursive parametric datatypes.

- `symbol` The name of the sort.
- `arity` The number of sort parameters of the sort.
-/
extern_def mkUnresolvedDatatypeSort :
  TermManager → (symbol : String) → (arity : Nat := 0) → Env cvc5.Sort

/-- Create a nullable sort.

- `sort` The sort of the element of the nullable.
-/
extern_def mkNullableSort : TermManager → (sort : cvc5.Sort) → Env cvc5.Sort

/-- Create a sort parameter.

- `symbol` The name of the sort.

**Warning**: This function is experimental and may change in future versions.
-/
extern_def mkParamSort : TermManager → (symbol : String) → Env cvc5.Sort



/-- Create a Boolean constant.

- `b`: The Boolean constant.
-/
extern_def mkBoolean : TermManager → (b : Bool) → Env Term

/-- Create a Boolean true constant. -/
extern_def mkTrue : TermManager → Env Term

/-- Create a Boolean false constant. -/
extern_def mkFalse : TermManager → Env Term

/-- Create a constant representing the number Pi. -/
extern_def mkPi : TermManager → Env Term

/-- Create an integer-value term.

- `s`: the string representation of the constant, may represent an integer such as (`"123"`).
-/
extern_def mkIntegerOfString : TermManager → (s : String) → Env Term
with
  /-- Create an integer-value term. -/
  mkInteger (tm : TermManager) : Int → Env Term := mkIntegerOfString tm ∘ toString

/-- Create a real-value term.

- `s`: the string representation of the constant, may represent an integer (`"123"`) or a real
  constant (`"12.34"`, `"12/34"`).
-/
extern_def mkRealOfString : TermManager → (s : String) → Env Term
with
  /-- Create a real-value term from a `Rat`. -/
  mkRealOfRat (tm : TermManager) (rat : Rat) : Env Term :=
    mkRealOfString tm s!"{rat.num}/{rat.den}"
  /-- Create a real-value term from numerator/denominator `Int`-s. -/
  mkReal (tm : TermManager)
    (num : Int) (den : Int := 1) (den_ne_0 : den ≠ 0 := by simp <;> omega)
  : Env Term :=
    let (num, den) :=
      match h : den with
      | .ofNat 0 => by contradiction
      | .ofNat den => (num, den)
      | .negSucc denMinus1 => (-num, denMinus1.succ)
    mkRealOfRat tm <| mkRat num den

/-- Create a regular expression all (re.all) term. -/
extern_def mkRegexpAll : TermManager → Env Term

/-- Create a regular expression allchar (re.allchar) term. -/
extern_def mkRegexpAllchar : TermManager → Env Term

/-- Create a regular expression none (re.none) term. -/
extern_def mkRegexpNone : TermManager → Env Term

/-- Create a constant representing an empty set of the given sort.

- `sort` The sort of the set elements.
-/
extern_def mkEmptySet : TermManager → (sort : cvc5.Sort) → Env Term

/-- Create a constant representing an empty bag of the given sort.

- `sort` The sort of the bag elements.
-/
extern_def mkEmptyBag : TermManager → (sort : cvc5.Sort) → Env Term

/-- Create a separation logic empty term. -/
extern_def mkSepEmp : TermManager → Env Term

/-- Create a separation logic nil term.

- `sort` The sort of the nil term.

**Warning**: this function is experimental and may change in future versions.
-/
extern_def mkSepNil : TermManager → (sort : cvc5.Sort) → Env Term

/-- Create a string constant from a `String`.

The string may contain SMT-LIB-compatible escape sequences like `\u1234` to encode unicode
characters.

- `s` The string this constant represents.
- `useEscSequences` Determines whether escape sequences in `s` should be converted to the
  corresponding unicode characters, default `false`.
-/
extern_def mkString : TermManager → (s : String) → (useEscSequences : Bool := false) → Env Term

/-- Create an empty sequence of the given element sort.

- `sort` The element sort of the sequence.
-/
extern_def mkEmptySequence : TermManager → (sort : cvc5.Sort) → Env Term

/-- Create a universe set of the given sort.

- `sort` The sort of the set elements.
-/
extern_def mkUniverseSet : TermManager → (sort : cvc5.Sort) → Env Term

/-- Create a bit-vector constant of given size and value.

The given value must fit into a bit-vector of the given size.

- `size` The bit-width of the bit-vector sort.
- `val` The value of the constant.
-/
extern_def mkBitVector : TermManager → (size : UInt32) → (val : UInt64 := 0) → Env Term

/-- Create a bit-vector constant of a given bit-width from a given string of base 2, 10, or 16.

The given value must fit into a bit-vector of the given size.

- `size` The bit-width of the bit-vector sort.
- `s` The string representation of the constant.
- `val` The base of the string representation: `2` for binary, `10` for decimal, and `16` for
  hexadecimal.
-/
extern_def mkBitVectorOfString :
  TermManager → (size : UInt32) → (s : String) → (base : UInt32) → Env Term

/-- Create a finite field constant in a given field from a given string of base n.

If `size` is the field size, the constant needs not be in range `[0,size)`. If it is outside this
range, it will be reduced modulo size before being constructed.

- `value` The string representation of the constant.
- `sort` The field sort.
- `base` The base of the string representation of `value`, default `10`.
-/
extern_def mkFiniteFieldElemOfString :
  TermManager → (value : String) → (sort : cvc5.Sort) → (base : UInt32 := 10) → Env Term
with
  mkFiniteFieldElem (tm : TermManager) (value : Int) (sort : cvc5.Sort) : Env Term :=
    tm.mkFiniteFieldElemOfString (base := 10) (toString value) sort

/-- Create a constant array with the provided constant value stored at every index.

- `sort` The sort of the constant array (must be an array sort).
- `val` The constant value to store (must match the sort's element sort).
-/
extern_def mkConstArray : TermManager → (sort : cvc5.Sort) → (val : Term) → Env Term

/-- Create a positive infinity floating-point constant (SMT-LIB: `+oo`).

- `exp` Number of bits in the exponent.
- `sig` Number of bits in the significand.
-/
extern_def mkFloatingPointPosInf : TermManager → (exp sig : UInt32) → Env Term

/-- Create a negative infinity floating-point constant (SMT-LIB: `-oo`).

- `exp` Number of bits in the exponent.
- `sig` Number of bits in the significand.
-/
extern_def mkFloatingPointNegInf : TermManager → (exp sig : UInt32) → Env Term

/-- Create a not-a-number floating-point constant (SMT-LIB: `NaN`).

- `exp` Number of bits in the exponent.
- `sig` Number of bits in the significand.
-/
extern_def mkFloatingPointNaN : TermManager → (exp sig : UInt32) → Env Term

/-- Create a positive zero floating-point constant (SMT-LIB: `+zero`).

- `exp` Number of bits in the exponent.
- `sig` Number of bits in the significand.
-/
extern_def mkFloatingPointPosZero : TermManager → (exp sig : UInt32) → Env Term

/-- Create a negative zero floating-point constant (SMT-LIB: `-zero`).

- `exp` Number of bits in the exponent.
- `sig` Number of bits in the significand.
-/
extern_def mkFloatingPointNegZero : TermManager → (exp sig : UInt32) → Env Term

/-- Create a rounding mode value.

- `rm` The floating point rounding mode this constant represents.
-/
extern_def mkRoundingMode : TermManager → (rm : RoundingMode) → Env Term

/-- Create a floating-point value from a bit-vector given in IEEE-754 format.

- `exp` Size of the exponent.
- `sig` Size of the significand.
- `val` Value of the floating-point constant as a bit-vector term.
-/
extern_def mkFloatingPoint : TermManager → (exp sig : UInt32) → (val : Term) → Env Term

/-- Create a floating-point value from its three IEEE-754 bit-vector value components.

- `sign` The sign bit.
- `exp` The bit-vector representing the exponent.
- `sig` The bit-vector representing the significand.
-/
extern_def mkFloatingPointOfComponents : TermManager → (sign exp sig : Term) → Env Term

/-- Create a cardinality constraint for an uninterpreted sort.

**Warning**: this function is experimental and may change in future versions.

- `sort` The sort the cardinality constraint is for.
- `upperBound` The upper bound on the cardinality of the sort.
-/
extern_def mkCardinalityConstraint :
  TermManager → (sort : cvc5.Sort) → (upperBound : UInt32) → Env Term

/-- Create a tuple term.

- `terms` The elements in the tuple.
-/
extern_def mkTuple : TermManager → (terms : Array Term) → Env Term

/-- Create a nullable some term.

- `term` The element value.
-/
extern_def mkNullableSome : TermManager → (term : Term) → Env Term

/-- Create a selector for nullable term.

- `term` A nullable term.
-/
extern_def mkNullableVal : TermManager → (term : Term) → Env Term

/-- Create a null tester for a nullable term.

- `term` A nullable term.
-/
extern_def mkNullableIsNull : TermManager → (term : Term) → Env Term

/-- Create a some tester for a nullable term.

- `term` A nullable term.
-/
extern_def mkNullableIsSome : TermManager → (term : Term) → Env Term

/-- Create a constant representing a null of the given sort.

- `sort` The sort of the nullable element.
-/
extern_def mkNullableNull : TermManager → (sort : cvc5.Sort) → Env Term

/-- Create a term that lifts kind to nullable terms.

- `kind` The lifted operator.
- `args` The arguments of the lifted operator.

Example: if we have the term `((_ nullable.lift +) x y)`, with `x` and `y` of type `(Nullable Int)`,
then `kind` would be `Kind.ADD`, and `args` would be `#[x, y]`. This function would return
`(nullable.lift (lambda ((a Int) (b Int)) (+ a b)) x y)`
-/
extern_def mkNullableLift : TermManager → (kind : Kind) → (args : Array Term) → Env Term

/-- Create n-ary term of given kind.

- `kind` The kind of the term.
- `children` The children of the term.
-/
extern_def mkTerm : TermManager → (kind : Kind) → (children : Array Term := #[]) → Env Term

/-- Create n-ary term of given kind from a given operator.

Create operators with `mkOp`.

- `op` The operator.
- `children` The children of the term.
-/
extern_def mkTermOfOp : TermManager → (op : Op) → (children : Array Term := #[]) → Env Term

/-- Create a free constant.

Note that the returned term is always fresh, even if the same arguments were provided on a
previous call to `mkConst`.

- `sort` The sort of the constant.
- `symbol` The name of the constant (optional).
-/
extern_def mkConst : TermManager → (srt : cvc5.Sort) → (name : String := "") → Env Term

/--
Create a bound variable to be used in a binder (i.e., a quantifier, a lambda, or a witness binder).

Note that the returned term is always fresh, even if the same arguments were provided on a previous
call to `mkVar`.

- `sort` The sort of the variable.
- `symbol` The name of the variable (optional).
-/
extern_def mkVar : TermManager → (srt : cvc5.Sort) → (name : String := "") → Env Term

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
extern_def mkOpOfIndices : TermManager → (kind : Kind) → (args : Array Nat := #[]) → Env Op
with mkOp := @mkOpOfIndices

/--Create operator of kind `Kind.DIVISIBLE` to support arbitrary precision integers.

See `cvc5.Kind` for a description of the parameters.

- `kind` The kind of the operator.
- `arg` The string argument to this operator.
-/
extern_def mkOpOfString : TermManager → (kind : Kind) → (arg : String) → Env Op

/-- Create a datatype constructor declaration.

- `name` The name of the datatype constructor.
-/
extern_def mkDatatypeConstructorDecl : TermManager → (name : String) → Env DatatypeConstructorDecl

/-- Create a datatype declaration.

- `name` The name of the datatype.
- `params` A list of sort parameters.
- `isCoDatatype` True if a codatatype is to be constructed.
-/
extern_def mkDatatypeDecl : TermManager → (name : String) →
  (params : Array cvc5.Sort := #[]) → (isCoDatatype : Bool := false) → Env DatatypeDecl

/-- Create a datatype sort.

- `dtypeDecl` The datatype declaration from which the sort is created.
-/
extern_def mkDatatypeSort : TermManager → (dtypeDecl : DatatypeDecl) → Env cvc5.Sort

/-- Create a vector of datatype sorts.

The names of the datatype declarations must be distinct.

- `dtypeDecls` The datatype declarations from which the sort is created.
-/
extern_def mkDatatypeSorts : TermManager → (dtypeDecls : Array DatatypeDecl) → Env (Array cvc5.Sort)

end TermManager

namespace EnvT

/-- Runs `EnvT` code. -/
def run [Monad m] [MonadLiftT BaseIO m] (code : EnvT m α) : m (Except Error α) := code

instance [Monad m] [MonadLiftT BaseIO m] : MonadLift Env (EnvT m) where
  monadLift code := do
    match ← liftM <| run code with
    | .ok a => return a
    | .error e => throw e

instance [Monad m] [MonadLiftT BaseIO m] : MonadLift IO (EnvT m) where
  monadLift code := do
    match ← code.toBaseIO with
    | .ok a => return a
    | .error e => throw <| Error.error <| toString e

end EnvT

@[inherit_doc EnvT.run]
protected abbrev run := @EnvT.run

namespace Env

@[inherit_doc EnvT.run]
def run : Env α → BaseIO (Except Error α) := cvc5.run

/-- Runs `Env` code in the `IO` monad, throws `cvc5.Error`s as `IO.Error`s. -/
def runIO (code : Env α) : IO α := do
  match ← code.run with
  | .ok res => return res
  | .error e => throw <| IO.Error.userError <| toString e

end Env

namespace Grammar

/-- Determine if this is the null grammar. -/
extern_def isNull : Grammar → Bool

/-- Physical equality of two grammars. -/
protected extern_def beq : Grammar → Grammar → Bool

instance : BEq Grammar := ⟨Grammar.beq⟩

/-- Hash function for grammar. -/
protected extern_def hash : Grammar → UInt64

instance : Hashable Grammar := ⟨Grammar.hash⟩

/-- Add `rule` to the set of rules corresponding to `ntSymbol`.

- `ntSymbol` The non-terminal to which the rule is added.
- `rule` The rule to add.
-/
extern_def addRule : Grammar → (ntSymbol : Term) → (rule : Term) → Env Grammar

/-- Add `rules` to the set of rules corresponding to `ntSymbol`.

- `ntSymbol` The non-terminal to which the rules are added.
- `rules` The rules to add.
-/
extern_def addRules : Grammar → (ntSymbol : Term) → (rules : Array Term) → Env Grammar

/-- Allow `ntSymbol` to be an arbitrary constant.

- `ntSymbol` The non-terminal allowed to be any constant.
-/
extern_def addAnyConstant : Grammar → (ntSymbol : Term) → Env Grammar

/-- Allow `ntSymbol` to be any input variable to corresponding *synth-fun*/*synth-inv* with the same
  sort as `ntSymbol`.

- `ntSymbol` The non-terminal allowed to be any input variable.
-/
extern_def addAnyVariable : Grammar → (ntSymbol : Term) → Env Grammar

end Grammar

namespace Command

/-- True if the command is null. -/
extern_def isNull : Command → Bool

/-- Get the name for this command, e.g., `"assert"`. -/
protected extern_def getCommandName : Command → String

/-- Invoke the command on the solver and symbol manager sm, prints the result to a string.

- `solver` The solver to invoke the command on.
- `sm` The symbol manager to invoke the command on.
-/
extern_def invoke : Command → Solver → SymbolManager → Env String

end Command

namespace SymbolManager

/-- Determine if the logic of this symbol manager has been set. -/
extern_def isLogicSet : SymbolManager → Env Bool

/-- Get the logic configured for this symbol manager.

Asserts `SymbolManager.isLogicSet`.
-/
extern_def getLogic : SymbolManager → Env String

/-- Get the list of sorts that have been declared via `declare-sort` commands.

These are the sorts that are printed as part of a response to a `get-model` command.
-/
extern_def getDeclaredSorts : SymbolManager → Env (Array cvc5.Sort)

/-- Get the list of terms that have been declared via `declare-fun` and `declare-const`.

These are the terms that are printed in response to a `get-model` command.
-/
extern_def getDeclaredTerms : SymbolManager → Env (Array Term)

/-- Get a mapping from terms to names that have been given to them via the `:named` attribute. -/
extern_def getNamedTerms : SymbolManager → Env (Array (Term × String))

end SymbolManager

namespace InputParser

/-- Get the associated symbol manager of this input parser. -/
extern_def getSymbolManager : InputParser → Env SymbolManager

/-- Is this parser done reading input? -/
extern_def isDone : InputParser → Env Bool

/-- Configure given file as input.

- `fileName` The name of the file to configure.
- `lang` The input language of the input string, default `InputLanguage::SMT_LIB_2_6`.
-/
extern_def setFileInput :
  InputParser → (fileName : String) → (lang : InputLanguage := .SMT_LIB_2_6) → Env Unit

/-- Configure a given concrete input string as the input to this parser.

- `input` The input string.
- `lang` The input language of the input string, default `InputLanguage::SMT_LIB_2_6`.
- `name` The name to use as input stream name for error messages, default `"lean-cvc5"`.
-/
extern_def setStringInput : InputParser → String →
  (lang : InputLanguage := .SMT_LIB_2_6) → (name : String := "lean-cvc5") → Env Unit

/-- Configure that we will be feeding strings to this parser via `appendIncrementalStringInput`.

- `lang` The input language, default `InputLanguage::SMT_LIB_2_6`.
- `name` The name of the stream, for use in error messages, default `"lean-cvc5"`.
-/
extern_def setIncrementalStringInput :
  InputParser → (lang : InputLanguage := .SMT_LIB_2_6) → (name : String := "lean-cvc5") → Env Unit

/-- Append string to the input being parsed by this parser. Should be called after calling
`setIncrementalStringInput`.

- `input` The input string.
-/
extern_def appendIncrementalStringInput : InputParser → (input : String) → Env Unit

/-- Parse and return the next command.

Will initialize the logic to "ALL" or the forced logic if no logic is set prior to this point and a
command is read that requires initializing the logic.
-/
extern_def nextCommand : InputParser → Env Command
  with
    /-- Parse and returns the next command if any, or `none` if the parser is at end-of-input. -/
    nextCommand? (parser : InputParser) : Env (Option Command) := do
      let cmd ← parser.nextCommand
      if cmd.isNull then return none else return cmd

/-- Parse and return the next term. Requires setting the logic prior to this point. -/
extern_def nextTerm : InputParser → Env Term
  with
    /-- Parse and returns the next term if any, or `none` if the parser is at end-of-input. -/
    nextTerm? (parser : InputParser) : Env (Option Term) := do
      let term ← parser.nextTerm
      if term.isNull then return none else return term

end InputParser

namespace Solver

/-- Get a string representation of the version of this solver. -/
extern_def getVersion : (solver : Solver) → Env String

/-- Set option.

- `option`: The option name.
- `value`: The option value.
-/
extern_def setOption : (solver : Solver) → (option value : String) → Env Unit

/-- Push (a) level(s) to the assertion stack.

```smtlib
(push <numeral>)
```

- `nscopes`: The number of levels to push.
-/
extern_def push : (solver : Solver) → (nscopes : UInt32 := 1) → Env Unit

/-- Remove all assertions. -/
extern_def resetAssertions : (solver : Solver) → Env Unit

/-- Set info.

```smtlib
(set-info <attribute>)
```

- `keyword`: The info flag.
- `value`: The value of the info flag.
-/
extern_def setInfo : (solver : Solver) → (keyword value : String) → Env Unit

/-- Set logic.

- `logic`: The logic to set.
-/
extern_def setLogic : (solver : Solver) → (logic : String) → Env Unit

/-- Determine if `setLogic` has been called. -/
extern_def isLogicSet : (solver : Solver) → Env Bool

/-- Get the logic set the solver.

Asserts `isLogicSet`.
-/
extern_def getLogic : (solver : Solver) → Env String
  with
    /-- The logic previously set if any, `none` otherwise. -/
    getLogic? (solver : Solver) : Env (Option String) := do
      if ← solver.isLogicSet then solver.getLogic else return none

/-- Simplify a term or formula based on rewriting and (optionally) applying substitutions for
solved variables.

If `applySubs` is true, then for example, if `(= x 0)` was asserted to this solver, this function
may replace occurrences of `x` with `0`.

- `t` The term to simplify.
- `applySubs` True to apply substitutions for solved variables.
-/
extern_def simplify : (solver : Solver) → (term : Term) → (applySubs : Bool := false) → Env Term

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
extern_def declareFun (solver : Solver)
  (symbol : String) (sorts : Array cvc5.Sort) (sort : cvc5.Sort) (fresh := true) : Env Term

/-- Assert a formula.

- `term`: The formula to assert.
-/
extern_def assertFormula : (solver : Solver) → Term → Env Unit

/-- Check satisfiability. -/
extern_def checkSat : (solver : Solver) → Env Result

/-- Check satisfiability assuming the given formulas.

- `assumptions`: The formulas to assume.
-/
extern_def checkSatAssuming : (solver : Solver) → (assumptions : Array Term) → Env Result

/-- Declare uninterpreted sort.

```smtlib
(declare-sort <symbol> <numeral>)
```

- `symbol`: The name of the sort.
- `arity`: The arity of the sort.
- `fresh`: If true, then this function always returns a new sort. Otherwise, it will always return
  the same sort for each call with the given arity and symbol where `fresh` is `false`.
-/
extern_def declareSort :
  (solver : Solver) → (symbol : String) → (arity : UInt32) → (fresh : Bool := true)
  → Env cvc5.Sort

/-- Define n-ary function.

```smtlib
(define-fun <function_def>)
```

- `symbol`: The name of the function.
- `boundVars`: The parameters to this function.
- `sort`: The sort of the return value of this function.
- `body`: The function body.
- `global`: Determines whether this definition is global (*i.e.* persists when popping the context).
-/
extern_def defineFun : (solver : Solver)
  → (symbol : String) → (boundVars : Array Term) → (sort : cvc5.Sort) → (body : Term)
  → (global : Bool := false)
  → Env Term

/-- Define recursive function.

```smtlib
(define-fun-rec <function_def>)
```

- `symbol`: The name of the function.
- `boundVars`: The parameters to this function.
- `sort`: The sort of the return value of this function.
- `body`: The function body.
- `global`: Determines whether this definition is global (*i.e.* persists when popping the context).
-/
extern_def defineFunRec : (solver : Solver)
  → (symbol : String) → (boundVars : Array Term) → (sort : cvc5.Sort) → (body : Term)
  → (global : Bool := false)
  → Env Term

/-- Define recursive function.

```smtlib
(define-fun-rec <function_def>)
```

Create parameter `fn` with `TermManager.mkConst`.

- `fn`: The sorted function.
- `bound_vars`: The parameters to this function.
- `term` The function body.
- `global` Determines whether this definition is global (*i.e.* persists when popping the context).
-/
extern_def defineFunRecTerm : (solver : Solver)
  → (fn : Term) → (boundVars : Array Term) → (body : Term)
  → (global : Bool := false)
  → Env Term

/-- Define recursive functions.

```smtlib
(define-funs-rec
  ( <function_decl>_1 ... <function_decl>_n )
  (     <body>_1      ...     <body>_n      )
)
```

- `funs`: The sorted functions, each created with `TermManager.mkConst`.
- `boundVars`: The list of parameters to the functions.
- `bodies`: The list of function bodies of the functions.
- `global`: Determines whether this definition is global (*i.e.* persists when popping the context).
-/
extern_def defineFunsRec : (solver : Solver)
  → (funs : Array Term) → (boundVars : Array (Array Term)) → (bodies : Array Term)
  → (global : Bool := false)
  → Env Unit

/-- Get the list of asserted formulas.

```smtlib
(get-assertions)
```
-/
extern_def getAssertions : (solver : Solver) → Env (Array Term)

/-- Get info from the solver.

```smtlib
(get-info <info_flag>)
```

- `flag`: The info flag.
-/
extern_def getInfo : (solver : Solver) → (flag : String) → Env String

/-- Get the value of a given option.

```smtlib
(get-option <keyword>)
```

- `option`: The option for which the value is queried.
-/
extern_def getOption : (solver : Solver) → (option : String) → Env String

/-- Get all option names that can be used with `setOption`, `getOption`, and `getOptionInfo`. -/
extern_def getOptionNames : (solver : Solver) → Env (Array String)

/-- Get the set of unsat (*failed*) assumptions.

```smtlib
(get-unsat-assumptions)
```

Requires to enable option `produce-unsat-assumption`.
-/
extern_def getUnsatAssumptions : (solver : Solver) → Env (Array Term)

/-- Create datatype sort.

```smtlib
(declare-datatype <symbol> <datatype_decl>)
```

- `symbol`: The name of the datatype sort.
- `ctors`: The constructor declarations of the datatype sort.
-/
extern_def declareDatatype :
  (solver : Solver) → (symbol : String) → (ctors : Array DatatypeConstructorDecl) → Env cvc5.Sort

/--
Get the unsatisfiable core.

SMT-LIB:

\verbatim embed:rst:leading-asterisk
.. code:: smtlib

  (get-unsat-core)

Requires to enable option `produce-unsat-cores`.

Note: In contrast to SMT-LIB, cvc5's API does not distinguish between named and
unnamed assertions when producing an unsatisfiable core. Additionally, the API
allows this option to be called after a check with assumptions. A subset of
those assumptions may be included in the unsatisfiable core returned by this
function.

Returns a set of terms representing the unsatisfiable core.
-/
extern_def getUnsatCore : (solver : Solver) → Env (Array Term)

/-- Get the lemmas used to derive unsatisfiability.

```smtlib
(get-unsat-core-lemmas)
```

Requires the SAT proof unsat core mode, so to enable option `unsat-cores-mode=sat-proof`.

**Warning**: this function is experimental and may change in future versions.
-/
extern_def getUnsatCoreLemmas : (solver : Solver) → Env (Array Term)

/-- Get a timeout core.

This function computes a subset of the current assertions that couse a timeout. It may make multiple
checks for satisfiability internally, each limited by the timeout value given by
`timeout-core-timeout`.

If the result is unknown and the reason is timeout, then returned the set of assertions corresponds
to a subset of the current assertions that cause a timeout in the specified time
`timeout-core-timeout`. If the result is unsat, then the list of formulas correspond to an unsat
core for the current assertions. Otherwise, the result is sat, indicating that the current
assertions are satisfiable, and the returned set of assertions is empty.

```smtlib
(get-timeout-core)
```

**Warning**: this function is experimental and may change in future versions.
-/
extern_def getTimeoutCore : (solver : Solver) → Env (Result × Array Term)

/-- Get a timeout core of the given assumptions.

This function computes a subset of the current assertions that couse a timeout when added to the
current assertions `timeout-core-timeout`.

If the result is unknown and the reason is timeout, then returned the set of assertions corresponds
to a subset of the given assertions that cause a timeout when added to the current assertions in the
specified time `timeout-core-timeout`. If the result is unsat, then the set of assumptions together
with the current assertions correspond to an unsat core for the current assertions. Otherwise, the
result is sat, indicating that the given assumptions plus the current assertions are satisfiable,
and the returned set of assertions is empty.

**NB:** this command does not require being preceeded by a call to `checkSat`.

```smtlib
(get-timeout-core (<assert>*))
```

**Warning**: this function is experimental and may change in future versions.
-/
extern_def getTimeoutCoreAssuming :
  (solver : Solver) → (assumptions : Array Term) → Env (Result × Array Term)

/-- Get a proof associated with the most recent call to `checkSat`.

Requires to enable option `produce-proofs`.

```smtlib
(get-proof :c)
```

**NB:** requires to enable option `produce-proofs`.

**Warning**: this function is experimental and may change in future versions.

- `c`: The component of the proof to return.
-/
extern_def getProof :
  (solver : Solver) → (c : ProofComponent := ProofComponent.FULL) → Env (Array Proof)

/--
Get the values of the given term in the current model.

SMT-LIB:

\verbatim embed:rst:leading-asterisk
.. code:: smtlib

    (get-value ( <term>* ))
\endverbatim

- `terms`: The term for which the value is queried.
-/
extern_def getValue (solver : Solver) (term : Term) : Env Term

/--
Get the values of the given terms in the current model.

SMT-LIB:

\verbatim embed:rst:leading-asterisk
.. code:: smtlib

    (get-value ( <term>* ))
\endverbatim

- `terms`: The terms for which the values are queried.
-/
extern_def getValues (solver : Solver) (terms : Array Term) : Env (Array Term)

/--
Get the domain elements of an uninterpreted sort in the current model.

The current model interprets the uninterpreted sort `s` as a finite sort whose domain elements are given in the return value of this function.

- `s`: The uninterpreted sort in question.
-/
extern_def getModelDomainElements (solver : Solver) (s : cvc5.Sort) : Env (Array Term)

/-- Determine if the model value of the given free constant was essential for showing
satisfiability of the last `checkSat` query based on the current model.

For any free constant `v`, this will only return false if `model-cores` has been set to true.

**Warning**: this function is experimental and may change in future versions.

- `v`: The term in question.
-/
extern_def isModelCoreSymbol : (solver : Solver) → (v: Term) → Env Bool

/-- Get the model.

```smtlib
(get-model)
```

Requires to enable option `produce-models`.

**Warning**: this function is experimental and may change in future versions.

- `sorts`: The list of uninterpreted sorts that should be printed in the model.
- `consts`: The list of free constants that should be printed in the model. A subset of these may be
  printed based on `isModelCoreSymbol`.
-/
extern_def getModel :
  (solver : Solver) → (sorts : Array cvc5.Sort) → (consts : Array Term) → Env String

/-- Do quantifier elimination.

```smtlib
(get-qe <q>)
```

**NB:** Quantifier elimination is only complete for logics such as LRA, LIA, and BV.

**Warning**: this function is experimental and may change in future versions.

- `q`: A quantified formula of the form `QX_1 ... QX_n, P(x_1...x_i, y_1...y_j)` where `QX` is a set
  of quantified variables of the form `Q x_1...x_k` and `P(x_1...x_i, y_1...y_j)` is a
  quantifier-free formula.

Returns a formula `Φ` such that, given the current set of formulas `A` asserted to this solver:
- `(a ∧ Q)` and (A ∧ Φ) are equivalent, and
- `Φ` is a quantifier-free formula containing only free variables in `y_1...y_n`.
-/
extern_def getQuantifierElimination : (solver : Solver) → (q : Term) → Env Term

/-- Do partial quantifier elimination, which can be used for incrementally computing the result of a
  quantifier elimination.

```smtlib
(get-qe-disjunct <q>)
```


**NB:** Quantifier elimination is only complete for logics such as LRA, LIA, and BV.

**Warning**: this function is experimental and may change in future versions.

- `q`: A quantified formula of the form `QX_1 ... QX_n, P(x_1...x_i, y_1...y_j)` where `QX` is a set
  of quantified variables of the form `Q x_1...x_k` and `P(x_1...x_i, y_1...y_j)` is a
  quantifier-free formula.

Returns a formula `Φ` such that, given the current set of formulas `A` asserted to this solver:
- `A ∧ q → A ∧ Φ` if `Q` is `∀`, and `A ∧ Φ → A ∧ q` if `Q` is `∃`;
- `Φ` is a quantifier-free formula containing only free variables in `y_1...y_n`;
- if `Q` is `∃`, let `A ∧ Q_n` be the formula `A ∧ ¬ (Φ ∧ Q_1) ∧ ... ∧ ¬ (Φ ∧ Q_n)` where for each
  `i ∈ [1, n]`, formula `Φ ∧ Q_i` is the result of calling `getQuantifierEliminationDisjunct` for
  `q` with the set of assertions `A ∧ Q_{i-1}`.

  Similarly, if `Q` is `∀`, then let `A ∧ Q_n` be `A ∧ (Φ ∧ Q_1) ∧ ... ∧ (Φ ∧ Q_n)` where `Φ ∧ Q_i`
  is the same as above.

  In either case, we have that `Φ ∧ Q_j` will eventually be true or false, for some finite `j`.
-/
extern_def getQuantifierEliminationDisjunct : (solver : Solver) → (q : Term) → Env Term

/-- When using separation logic, sets the location sort and the datatype sort to the given ones.

This function should be invoked exactly once, before any separation logic constraints are provided.

**Warning**: this function is experimental and may change in future versions.

- `locSort`: The location sort of the heap.
- `dataSort`: The data sort of the heap.
-/
extern_def declareSepHeap :
  (solver : Solver) → (locSort : cvc5.Sort) → (dataSort : cvc5.Sort) → Env Unit

/-- When using separation logic, obtain the term for the heap.

**Warning**: this function is experimental and may change in future versions.
-/
extern_def getValueSepHeap : (solver : Solver) → Env Term

/-- When using separation logic, obtain the term for nil.

**Warning**: this function is experimental and may change in future versions.
-/
extern_def getValueSepNil : (solver : Solver) → Env Term

/-- Declare a symbolic pool of terms with the given initial value.

For details on how pools are used to specify instructions for quantifier instantiation, see
`Kind.INST_POOL`

```smtlib
(declare-pool <symbol> <sort> ( <term>* ))
```

**Warning**: this function is experimental and may change in future versions.

- `symbol`: The name of the pool.
- `sort`: The sort of the elements of the pool.
- `initValue` The initial value of the pool.
-/
extern_def declarePool :
  (solver : Solver) → (symbol : String) → (sort : cvc5.Sort) → (initValue : Array Term) → Env Term

/-- Declare an oracle function with reference to an implementation.

Oracle functions have a different semantics with respect to ordinary declared functions. In
particular, for an input to be satisfiable, its oracle functions are implicitly universally
quantified.

This function is used in part for implementing this command:

```smtlib
(declare-oracle-fun <sym> ( <sort>* ) <sort> <sym>)
```

In particular, the above command is implemented by constructing a function over terms that wraps a
call to binary sym via a text interface.

**Warning**: this function is experimental and may change in future versions.

- `symbol`: The name of the oracle.
- `sorts`: The sorts of the parameters to this function.
- `sort`: The sort of the return value of this function.
- `fn`: The function that implements the oracle function.

# TODO

Causes the tests to crash in a very weird way, see `cvc5Test/Unit/ApiSolverOracleFun.lean`.
-/
extern_def declareOracleFun :
  (solver : Solver) → (symbol : String)
  → (sorts : Array cvc5.Sort) → (sort : cvc5.Sort)
  → (fn : Array Term → Env Term)
  → Env Term

/-- Pop (a) level(s) from the assertion stack.

```smtlib
(pop <numeral>)
```

- `nscopes`: The number of levels to pop.
-/
extern_def pop : (solver : Solver) → (nscopes : UInt32 := 1) → Env Unit

/-- Get an interpolant if one exists, the null term otherwise.

Given that `A → B` is valid, this function determines a term `I` over the shared variables of `A` and `B`, such that `A → I` and `I → B` are valid. `A` is the current set of assertions and `B` is the conjecture, given as `conj`.

```smtlib
(get-interpolant <symbol> <conj>)
```

**NB:** in SMT-LIB, `<symbol>` assigns a symbol to the interpolant.

**NB:** Requires option `produce-interpolants` to be set to a mode different from `none`.

**Warning**: this function is experimental and may change in future versions.

- `conj`: The conjecture term.
-/
extern_def getInterpolantSimple : (solver : Solver) → (conj : Term) → Env Term

/-- Get an interpolant if one exists, the null term otherwise.

Given that `A → B` is valid, this function determines a term `I` over the shared variables of `A`
and `B`, such that `A → I` and `I → B` are valid. `I` is constructed from the given grammar. `A` is
the current set of assertions and `B` is the conjecture, given as `conj`.

```smtlib
(get-interpolant <symbol> <conj> <grammar>)
```

**NB:** in SMT-LIB, `<symbol>` assigns a symbol to the interpolant.

**NB:** Requires option `produce-interpolants` to be set to a mode different from `none`.

**Warning**: this function is experimental and may change in future versions.

- `conj`: The conjecture term.
- `grammar`: The grammar for the interpolant `I`.
-/
extern_def getInterpolantOfGrammar :
  (solver : Solver) → (conj : Term) → (grammar : Grammar) → Env Term

/-- Get an interpolant if one exists, the null term otherwise.

Given that `A → B` is valid, this function determines a term `I` over the shared variables of `A`
and `B`, such that `A → I` and `I → B` are valid. If a grammar `G` is provided, `I` is constructed
from `G`. `A` is the current set of assertions and `B` is the conjecture, given as `conj`.

```smtlib
(get-interpolant <symbol> <conj>)
(get-interpolant <symbol> <conj> <grammar>)
```

**NB:** in SMT-LIB, `<symbol>` assigns a symbol to the interpolant.

**NB:** Requires option `produce-interpolants` to be set to a mode different from `none`.

**Warning**: this function is experimental and may change in future versions.

- `conj`: The conjecture term.
- `grammar`: The optional grammar for the interpolant `I`.
-/
def getInterpolant
  (solver : Solver) (conj : Term) (grammar : Option Grammar := none)
: Env Term :=
  if let some grammar := grammar
  then solver.getInterpolantOfGrammar conj grammar
  else solver.getInterpolantSimple conj

/-- Get the next interpolant if any, the null term otherwise.

Can only be called immediately after a successful call to `getInterpolant`,
`getInterpolantOfGrammar`, `getInterpolant?`, `getInterpolantNext`, or `getInterpolantNext`. It is
guaranteed to produce a syntactically different interpolant *w.r.t.* the last returned interpolant
if successful.

```smtlib
(get-interpolant-next)
```

Requires to enable incremental mode, and option `produce-interpolants` to be set to a mode different
from `none`.

**Warning**: this function is experimental and may change in future versions.

Returns a term `I` such that `A → I` and `I → B` and valid, where `A` is the current set of
assertions and `B` is given in the input by `conj`, or the null term if such a term cannot be found.
-/
extern_def getInterpolantNext : (solver : Solver) → Env Term

/-- Get an abduct if one exists, the null term otherwise.

```smtlib
(get-abduct <conj>)
```

**NB:** Requires to enable option `produce-abducts`.

**Warning**: this function is experimental and may change in future versions.

- `conj`: The conjecture term.

Returns a term `C` such that `A ∧ C` is satisfiable, and `A ∧ ¬B ∧ C` is unsatisfiable, where `A` is
the current set of assertions and `B` is given in the input by `conj`, or the null term if such a
term cannot be found.
-/
private extern_def getAbductSimple : (solver : Solver) → (conj : Term) → Env Term

/-- Get an abduct if one exists, the null term otherwise.

```smtlib
(get-abduct <conj> <grammar>)
```

**NB:** Requires to enable option `produce-abducts`.

**Warning**: this function is experimental and may change in future versions.

- `conj`: The conjecture term.
- `grammar`: The grammar for the abduct `C`.

Returns a term `C` such that `A ∧ C` is satisfiable, and `A ∧ ¬B ∧ C` is unsatisfiable, where `A` is
the current set of assertions and `B` is given in the input by `conj`, or the null term if such a
term cannot be found.
-/
extern_def getAbductOfGrammar :
  (solver : Solver) → (conj : Term) → (grammar : Grammar) → Env Term

/-- Get an abduct if one exists.

```smtlib
(get-abduct <conj>)
(get-abduct <conj> <grammar>)
```

**NB:** Requires to enable option `produce-abducts`.

**Warning**: this function is experimental and may change in future versions.

- `conj`: The conjecture term.
- `grammar`: The optional grammar for the abduct `C`.

Returns a term `C` such that `A ∧ C` is satisfiable, and `A ∧ ¬B ∧ C` is unsatisfiable, where `A` is
the current set of assertions and `B` is given in the input by `conj`, or the null term if such a
term cannot be found.
-/
def getAbduct
  (solver : Solver) (conj : Term) (grammar : Option Grammar := none)
: Env Term :=
  if let some grammar := grammar
  then solver.getAbductOfGrammar conj grammar
  else solver.getAbductSimple conj

/-- Get the next interpolant if any, the null term otherwise.

Can only be called immediately after a successful call to `getAbduct`, `getAbductOfGrammar`,
`getAbduct?`, `getAbductNext`, or `getAbductNext?`. It is guaranteed to produce a syntactically
different abduct *w.r.t.* the last returned abduct if successful.

```smtlib
(get-abduct-next)
```

Requires to enable incremental mode, and option `produce-abducts`.

**Warning**: this function is experimental and may change in future versions.

Returns a term `C` such that `A ∧ C` is satisfiable, and `A ∧ ¬B ∧ C` is unsatisfiable, where `A` is
the current set of assertions and `B` is given in the input by the last call to a `getAbduct`-like
function, or the null term if such a term cannot be found.
-/
extern_def getAbductNext : (solver : Solver) → Env Term

/-- Block the current model. Can be called only if immediately preceded by a SAT or INVALID query.

```smtlib
(block-model)
```

**NB:** requires enabling option `produce-models`.

**Warning**: this function is experimental and may change in future versions.

- `mode`: The mode to use for blocking.
-/
extern_def blockModel : (solver : Solver) → (mode : BlockModelsMode) → Env Unit

/-- Block the current model values of (at least) the values in `terms`.

Can be called only if immediately preceded by a SAT query.

```smtlib
(block-model-values ( <term>+ ))
```

**NB:** requires enabling option `produce-models`.

**Warning**: this function is experimental and may change in future versions.

- `terms`: The model values to block.
-/
extern_def blockModelValues : (solver : Solver) → (terms : Array Term) → Env Unit

/-- Produce a string containing information about all instantiations made by the quantifier module.

**Warning**: this function is experimental and may change in future versions.
-/
extern_def getInstantiations : (solver : Solver) → Env String

/-- Prints a proof as a string in a selected proof format mode.

Other aspects of printing are taken from the solver options.

**Warning**: this function is experimental and may change in future versions.

- `proof`: A proof, usually obtained from `getProof`.
- `format`: The proof format used to print the proof. Must be `ProofFormat.NONE` if the proof is
  from a component other than `ProofComponent.FULL`.
-/
extern_def proofToString :
  (solver : Solver) → (proof : Proof) → (format : ProofFormat := ProofFormat.DEFAULT) → Env String

/-- Get a list of learned literals that are entailed by the current set of assertions.

**Warning**: this function is experimental and may change in future versions.

- `t`: The type of learned literals to return.
-/
extern_def getLearnedLiterals :
  (solver : Solver) → (t : LearnedLitType := LearnedLitType.INPUT) → Env (Array Term)

/-- Create a Sygus grammar.

The first non-terminal is treated as the starting non-terminal, so the order of non-terminals
matters.

- `boundVars` The parameters to corresponding *synth-fun*/*synth-inv*.
- `ntSymbols` The pre-declaration of the non-terminal symbols.
-/
extern_def mkGrammar :
  Solver → (boundVars : Array Term) → (ntSymbols : Array Term) → Env Grammar

/-- Synthesize n-ary function.

SyGuS v2:

```smtlib
(synth-fun <symbol> ( <boundVars>* ) <sort>)
```

- `symbol` The name of the function.
- `boundVars` The parameters to this function.
- `sort` The sort of the return value of this function.
-/
private extern_def synthFunWithoutGrammar :
  Solver → (symbol : String) → (boundVars : Array Term) → (sort : cvc5.Sort) → Env Term

/-- Synthesize n-ary function following specified syntactic constraints.

SyGuS v2:

```smtlib
(synth-fun <symbol> ( <boundVars>* ) <sort> <grammar>)
```

- `symbol` The name of the function.
- `boundVars` The parameters to this function.
- `sort` The sort of the return value of this function.
- `grammar` The syntactic constraints.
-/
private extern_def synthFunWithGrammar : Solver →
  (symbol : String) → (boundVars : Array Term) → (sort : cvc5.Sort) → (grammar : Grammar) → Env Term

/-- Synthesizes an n-ary function with optional syntactic constraints to verify.

```smtlib
(synth-fun <symbol> ( <boundVars>* ) <sort>)
(synth-fun <symbol> ( <boundVars>* ) <sort> <grammar>)
```

- `symbol` The name of the function.
- `boundVars` The parameters to this function.
- `sort` The sort of the return value of this function.
- `grammar` The optional syntactic constraints.
-/
def synthFun (solver: Solver)
  (symbol : String) (boundVars : Array Term) (sort : cvc5.Sort)
  (grammar : Option Grammar := none)
: Env Term :=
  if let some grammar := grammar
  then solver.synthFunWithGrammar symbol boundVars sort grammar
  else solver.synthFunWithoutGrammar symbol boundVars sort

/-- Append \p symbol to the current list of universal variables.

SyGuS v2:

```smtlib
(declare-var <symbol> <sort>)
```

- `sort` The sort of the universal variable.
- `symbol` The name of the universal variable.
-/
extern_def declareSygusVar : Solver → (symbol : String) → (sort : cvc5.Sort) → Env Term

/-- Add a forumla to the set of Sygus constraints.

SyGuS v2:

```smtlib
(constraint <term>)
```

- `term` The formula to add as a constraint.
-/
extern_def addSygusConstraint : Solver → (term : Term) → Env Unit

/-- Get the list of sygus constraints. -/
extern_def getSygusConstraints : Solver → Env (Array Term)

/-- Add a forumla to the set of Sygus assumptions.

SyGuS v2:

```smtlib
(assume <term>)
```

- `term` The formula to add as an assumption.
-/
extern_def addSygusAssume : Solver → (term : Term) → Env Unit

/-- Get the list of sygus assumptions. -/
extern_def getSygusAssumptions : Solver → Env (Array Term)

/-- Add a set of Sygus constraints to the current state that correspond to an invariant synthesis
  problem.

SyGuS v2:

```smtlib
(inv-constraint <inv> <pre> <trans> <post>)
```

- `inv` The function-to-synthesize.
- `pre` The pre-condition.
- `trans` The transition relation.
- `post` The post-condition.
-/
extern_def addSygusInvConstraint : Solver → (inv pre trans post : Term) → Env Unit

/-- Try to find a solution for the synthesis conjecture corresponding to the current list of
  functions-to-synthesize, universal variables and constraints.

SyGuS v2:

```smtlib
(check-synth)
```

Returns the result of the check, which is *"solution"* if the check found a solution in which case
solutions are available via getSynthSolutions, *"no solution"* if it was determined there is no
solution, or *"unknown"* otherwise.
-/
extern_def checkSynth : Solver → Env SynthResult

/-- Try to find a next solution for the synthesis conjecture corresponding to the current list of
  functions-to-synthesize, universal variables and constraints.

Must be called immediately after a successful call to check-synth or check-synth-next. Requires
incremental mode.

SyGuS v2:

```smtlib
(check-synth-next)
```

Returns the result of the check, which is "solution" if the check found a solution in which case
solutions are available via getSynthSolutions, "no solution" if it was determined there is no
solution, or "unknown" otherwise.
-/
extern_def checkSynthNext : Solver → Env SynthResult

/-- Get the synthesis solution of the given term.

This function should be called immediately after the solver answers *unsat* for sygus input.

- `term` The term for which the synthesis solution is queried.
-/
extern_def getSynthSolution : Solver → (term : Term) → Env Term

/-- Get the synthesis solutions of the given terms.

This function should be called immediately after the solver answers *unsat* for sygus input.

- `terms` The terms for which the synthesis solutions is queried.
-/
extern_def getSynthSolutions : Solver → (term : Array Term) → Env (Array Term)

/-- Find a target term of interest using sygus enumeration, with no provided grammar.

The solver will infer which grammar to use in this call, which by default will be the grammars
specified by the function(s)-to-synthesize in the current context.

SyGuS v2:

```smtlib
(find-synth :target)
```

- `fst` The identifier specifying what kind of term to find.

Returns the result of the find, which is the null term if this call failed.

**Warning**: this function is experimental and may change in future versions.
-/
private extern_def findSynthWithoutGrammar : Solver → (fst : FindSynthTarget) → Env Term

/-- Find a target term of interest using sygus enumeration with a provided grammar.

SyGuS v2:

```smtlib
(find-synth :target G)
```

- `fst` The identifier specifying what kind of term to find.
- `grammar` The grammar for the term.

Returns the result of the find, which is the null term if this call failed.

**Warning**: this function is experimental and may change in future versions.
-/
private extern_def findSynthWithGrammar :
  Solver → (fst : FindSynthTarget) → (grammar : Grammar) → Env Term

/-- Find a target term of interest using sygus enumeration with an optional grammar.

SyGuS v2:

```smtlib
(find-synth)
(find-synth :target G)
```

- `fst` The identifier specifying what kind of term to find.
- `grammar` The optional grammar for the term. If `none`, the solver will infer which grammar to use
  in this call, which by default will be the grammars specified by the function(s)-to-synthesize in
  the current context.

Returns the result of the find, which is the null term if the call failed.

**Warning**: this function is experimental and may change in future versions.
-/
def findSynth (solver : Solver) (fst : FindSynthTarget)
  (grammar : Option Grammar := none)
: Env Term :=
  if let some grammar := grammar
  then solver.findSynthWithGrammar fst grammar
  else solver.findSynthWithoutGrammar fst

/-- Try to find a next target term of interest using sygus enumeration.

Must be called immediately after a successful call to find-synth or find-synth-next.

SyGuS v2:

```smtlib
(find-synth-next)
```

Returns the result of the find, which is the null term if this call failed.

**Warning**: this function is experimental and may change in future versions.
-/
extern_def findSynthNext : Solver → Env Term

end Solver

end cvc5

end
