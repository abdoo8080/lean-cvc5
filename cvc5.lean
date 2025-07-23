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
import cvc5.Types



/-! # Cvc5 low-level API -/
namespace cvc5



/-! ## Basic types -/



/-- Error type. -/
inductive Error where
  | missingValue
  | error (msg : String)
  | recoverable (msg : String)
  | unsupported (msg : String)
  | option (msg : String)
  | parsing (msg : String)
deriving Repr

namespace Error

def toIO : Error → IO.Error
  | .missingValue => IO.Error.userError "missing value"
  | .error msg => IO.Error.userError s!"{msg}"
  | .recoverable msg => IO.Error.userError s!"[recoverable] {msg}"
  | .unsupported msg => IO.Error.userError s!"[unsupported] {msg}"
  | .option msg => IO.Error.userError s!"[option] {msg}"
  | .parsing msg => IO.Error.userError s!"[parsing] {msg}"

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

section variable [Monad m] [MonadExcept Error m] (msg : String)

def throwMissingValue : m α := throw <| Error.missingValue

protected def throw : m α := throw <| Error.error msg
def throwRecoverable : m α := throw <| Error.recoverable msg
def throwUnsupported : m α := throw <| Error.unsupported msg
def throwOption : m α := throw <| Error.option msg
def throwParsing : m α := throw <| Error.parsing msg

end


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

namespace Result

instance : Nonempty Result := ResultImpl.property

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



/-! ## FFI constructor

The following constructors are only used by C++ to inject values as `Except Error _`.
-/
section ffi_except_constructors

/-- Only used by FFI to inject values. -/
@[export except_ok]
private def mkExceptOk {α : Type} : α → Except Error α := .ok

/-- Only used by FFI to inject values. -/
@[export except_ok_bool]
private def mkExceptOkBool : Bool → Except Error Bool := .ok

/-- Only used by FFI to inject values. -/
@[export except_ok_u32]
private def mkExceptOkU32 : UInt32 → Except Error UInt32 := .ok

/-- Only used by FFI to inject values. -/
@[export except_ok_u16]
private def mkExceptOkU16 : UInt16 → Except Error UInt16 := .ok

/-- Only used by FFI to inject values. -/
@[export except_ok_u8]
private def mkExceptOkU8 : UInt8 → Except Error UInt8 := .ok

/-- Only used by FFI to inject errors. -/
@[export except_err]
private def mkExceptErr {α : Type} : String → Except Error α :=
  .error ∘ Error.error

end ffi_except_constructors



/-! ## Environment, private `TermManager`, and `Solver`-related definitions -/



private opaque TermManagerImpl : NonemptyType.{0}

/-- Manager for cvc5 terms. -/
private def TermManager : Type := TermManagerImpl.type

namespace TermManager

instance : Nonempty TermManager := TermManagerImpl.property

@[extern "termManager_new"]
private opaque new : Unit → BaseIO TermManager

end TermManager


structure Env (ω : Type) (α : Type) where
private ofRaw ::
  toRaw : ReaderT cvc5.TermManager (ExceptT Error BaseIO) α

protected def run (code : {ω : Type} → Env ω α) : ExceptT Error BaseIO α := do
  let tm ← TermManager.new ()
  (@code Unit).toRaw tm

protected def runIO (code : {ω : Type} → Env ω α) : IO α := fun world =>
  match cvc5.run code world with
  | .ok (.ok res) world => .ok res world
  | .ok (.error err) world => .error err.toIO world

namespace Env

instance : Monad (Env ω) where
  pure := (⟨pure ·⟩)
  bind | ⟨code⟩, f => ⟨fun tm => code tm >>= (f · |>.toRaw tm)⟩

instance : MonadExcept Error (Env ω) where
  throw e := ⟨fun _ => throw e⟩
  tryCatch | ⟨code⟩, errorDo => ofRaw fun tm world =>
    match code tm world with
    | okay@(.ok (.ok _) _) => okay
    | error@(.error _ _) => error
    | .ok (.error e) world => errorDo e |>.toRaw tm world

instance : MonadLift (ST IO.RealWorld) (Env ω) where
  monadLift stCode := ofRaw fun _ => stCode

instance : MonadLift (Except Error) (Env ω) where
  monadLift excCode := ofRaw fun _ => excCode

instance : MonadLift IO (Env ω) where
  monadLift ioCode := ofRaw fun _ => do
    match ← ioCode.toBaseIO with
    | .ok res => return res
    | .error e => throw <| Error.error s!"[IO] {e}"

-- sanity
example : MonadLiftT BaseIO (Env ω) := inferInstance

private def managerDoM (f : TermManager → Env ω α) : Env ω α :=
  ofRaw fun tm => (f tm |>.toRaw tm)

private def managerDo? (f : TermManager → Except Error α) : Env ω α :=
  managerDoM (liftM ∘ f)

private def managerDo (f : TermManager → α) : Env ω α :=
  managerDoM (pure ∘ f)



/-!
helpers for C++ to produce `Env ω _` values.
-/

@[export ffi_env_pure]
private def ffi_env_pure (a : α) : Env ω α :=
  pure a

@[export ffi_env_pure_string]
private def ffi_env_pure_string (a : String) : Env ω String :=
  pure a

@[export ffi_env_throw]
private def ffi_env_throw (cppError : String) : Env ω α :=
  throw <| .error s!"[ffi] {cppError}"

end Env



namespace Solver

private opaque RawImpl : NonemptyType.{0}

/-- A cvc5 solver. -/
private def Raw : Type := RawImpl.type

namespace Raw

instance : Nonempty Raw := RawImpl.property

/-- Constructor.

Constructs solver instance from a given term manager instance.

- `tm`: The associated term manager.
-/
@[extern "solver_new"]
private opaque new : TermManager → Solver.Raw

end Raw


/-! ### Solver input parser -/

private opaque InputParserImpl : NonemptyType.{0}

/-- Solver input parser -/
private def InputParser : Type := InputParserImpl.type

namespace InputParser

instance : Nonempty InputParser := InputParserImpl.property

@[extern "inputParser_new"]
private opaque new : Solver.Raw → InputParser

@[extern "inputParser_parseCommands"]
private opaque parseCommands :
  (raw : Solver.Raw) → (inputParser : InputParser) → (query : String) → Except Error String

end InputParser

end Solver

structure Solver (ω : Type) where
private mk' ::
  /-- Underlying raw solver. -/
  private toRaw : Solver.Raw
  /-- Parser placeholder. -/
  private parser? : IO.Ref (Option Solver.InputParser)

namespace Solver

private def ofManager (tm : TermManager) : BaseIO (Solver ω) := do
  let parser? ← IO.mkRef none
  return {toRaw := Raw.new tm, parser?}

def new : Env ω (Solver ω) := Env.managerDoM (liftM ∘ ofManager)

section variable (solver : Solver ω)

private def rawSolverDo (f : Solver.Raw → Env ω α) : Env ω α :=
  f solver.toRaw

private def rawSolverDo? (f : Solver.Raw → Except Error α) : Env ω α :=
  solver.rawSolverDo (liftM ∘ f)

private def inputParserDoM (f : InputParser → Env ω α) : Env ω α := do
  if let some parser ← solver.parser?.get then f parser else
    let parser := InputParser.new solver.toRaw
    solver.parser?.set parser
    f parser

private def inputParser : Env ω InputParser := do
  if let some parser ← solver.parser?.get then
    return parser
  else
    let parser := InputParser.new solver.toRaw
    solver.parser?.set parser
    return parser

/-- Parses some SMT-LIB commands and returns the output.

- `commands` The SMT-LIB commands to parse.
- `catchErrors` If true, this function fails if the parser's output contains errors. Otherwise does
  not look at the output and simply returns it.
-/
def parseSmtLibWithOutput (commands : String) (catchErrors : Bool := true) : Env ω String := do
  let parser ← solver.inputParser
  let output ← parser.parseCommands solver.toRaw commands
  if catchErrors then
    let output := output.trim
    if let some err := output.splitOn "\n" |> findError? then
      cvc5.throwParsing s!"{err}\n\n```output\n{output}\n```"
  return output
where
  findError? : List String → Option String
    | line :: tail =>
      if line.trimLeft.startsWith "(error"
      then extractError none 0 (line :: tail)
      else findError? tail
    | [] => none
  extractError (err? : Option String) (paren : Int) : List String → String
    | line :: tail =>
      let paren := parenBalance line paren
      let err := err?.map (s!"{·}\n{line}") |>.getD line
      if paren = 0 then attemptErrorCleanup err
      else extractError err paren tail
    | [] => err? |>.getD "cannot extract parsing error: reached EOI"
  parenBalance (s : String) (current : Int) : Int := Id.run do
    let mut balance := current
    for i in [0:s.length] do
      match s.get ⟨i⟩ with
      | '(' => balance := balance + 1
      | ')' => balance := balance - 1
      | _ => pure ()
    return balance
  attemptErrorCleanup (s : String) :=
    let (pref, suff) := ("(error \"", "\")")
    if s.startsWith pref ∧ s.endsWith suff
    then s.drop pref.length |>.dropRight suff.length
    else s

/-- Parses some SMT-LIB commands.

Fails if an error is detected in the parser's output.
-/
def parseSmtLib (commands : String) : Env ω Unit := do
  let _output ← solver.parseSmtLibWithOutput commands (catchErrors := true)

end



/-!
Helpers for C++ to work with `Solver ω` values.
-/

@[export ffi_solver_to_raw]
private def ffi_solver_to_raw : Solver ω → Solver.Raw := toRaw

end Solver




private opaque SrtImpl : NonemptyType.{0}

/-- The sort of a cvc5 term. -/
@[irreducible]
def Srt : (ω : Type) → Type := fun _ => SrtImpl.type

namespace Srt

private theorem typeDef : Srt ω = SrtImpl.type :=
  by unfold Srt ; rfl

private def toImpl : (srt : Srt ω) → SrtImpl.type :=
  by rw [typeDef] ; exact id

private def ofImpl : (srt : SrtImpl.type) → Srt ω :=
  by rw [typeDef] ; exact id

instance instNonemptySort : Nonempty (Srt ω) :=
  by rw [typeDef] ; exact SrtImpl.property

/-- The null sort. -/
extern_def null' as "null" : Unit → Srt ω
@[inherit_doc null']
def null : Env ω (Srt ω) := pure <| null' ()

private instance : Inhabited (Srt ω) := ⟨null' ()⟩

/-- A string representation of this sort. -/
protected extern_def toString : Srt ω → String

instance : ToString (Srt ω) := ⟨Srt.toString⟩

instance : Repr (Srt ω) := ⟨fun self _ => self.toString⟩

/-- Comparison for structural equality. -/
protected extern_def beq : Srt ω → Srt ω → Bool

instance : BEq (Srt ω) := ⟨Srt.beq⟩

/-- Less than comparison. -/
protected extern_def blt : Srt ω → Srt ω → Bool

/-- Greater than comparison. -/
protected extern_def bgt : Srt ω → Srt ω → Bool

/-- Less than or equal comparison. -/
protected extern_def ble : Srt ω → Srt ω → Bool

/-- Greater than or equal comparison. -/
protected extern_def bge : Srt ω → Srt ω → Bool

/-- Comparison of two sorts. -/
protected def compare (s1 s2 : Srt ω) : Ordering :=
  if s1.beq s2 then .eq
  else if s1.bgt s2 then .gt
  else .lt

instance : Ord (Srt ω) := ⟨Srt.compare⟩

instance : LT (Srt ω) where
  lt := (Srt.blt · ·)

instance : DecidableLT (Srt ω) :=
  fun s1 s2 => if h : s1.blt s2 then .isTrue h else .isFalse h

instance : LE (Srt ω) where
  le := (Srt.ble · ·)

instance : DecidableLE (Srt ω) :=
  fun s1 s2 => if h : s1.ble s2 then .isTrue h else .isFalse h

/-- Hash function for cvc5 sorts. -/
protected extern_def hash : Srt ω → UInt64

instance : Hashable (Srt ω) := ⟨Srt.hash⟩

end Srt



private opaque TermImpl : NonemptyType.{0}

/-- A cvc5 term. -/
@[irreducible]
def Term : (ω : Type) → Type := fun _ => TermImpl.type

namespace Term

private theorem typeDef : Term ω = TermImpl.type :=
  by unfold Term ; rfl

private def toImpl : Term ω → TermImpl.type :=
  by rw [typeDef] ; exact id

private def ofImpl : TermImpl.type → Term ω :=
  by rw [typeDef] ; exact id

instance instNonemptyTerm : Nonempty (Term ω) :=
  by rw [typeDef] ; exact TermImpl.property

/-- The null term. -/
private extern_def null' as "null" : Unit → Term ω
@[inherit_doc null']
def null : Env ω (Term ω) := pure <| null' ()

instance : Inhabited (Term ω) := ⟨null' ()⟩

/-- A string representation of this term. -/
protected extern_def toString : Term ω → String

instance : ToString (Term ω) := ⟨Term.toString⟩

/-- Syntactic equality operator. -/
protected extern_def beq : (Term ω) → (Term ω) → Bool

instance : BEq (Term ω) := ⟨Term.beq⟩

protected extern_def hash : (Term ω) → UInt64

instance : Hashable (Term ω) := ⟨Term.hash⟩

/-- Determine if this term is nullary. -/
extern_def isNull : Term ω → Bool

end Term



private opaque OpImpl : NonemptyType.{0}

/-- A cvc5 term. -/
@[irreducible]
def Op : (ω : Type) → Type := fun _ => OpImpl.type

namespace Op

private theorem typeDef : Op ω = OpImpl.type :=
  by unfold Op ; rfl

private def toImpl : Op ω → OpImpl.type :=
  by rw [typeDef] ; exact id

private def ofImpl : OpImpl.type → Op ω :=
  by rw [typeDef] ; exact id

instance instNonemptyOp : Nonempty (Op ω) :=
  by rw [typeDef] ; exact OpImpl.property

/-- The null operator. -/
extern_def null' as "null" : Unit → Op ω
@[inherit_doc null']
def null : Env ω (Op ω) := pure <| null' ()

/-- Determine if this operator is nullary. -/
extern_def isNull : Op ω → Bool

instance : Inhabited (Op ω) := ⟨null' ()⟩

/-- A string representation of this term. -/
protected extern_def toString : Op ω → String

instance : ToString (Op ω) := ⟨Op.toString⟩

end Op



private opaque ProofImpl : NonemptyType.{0}

/-- A cvc5 proof.

Proofs are trees and every proof object corresponds to the root step of a proof. The branches of the
root step are the premises of the step.
-/
@[irreducible]
def Proof : (ω : Type) → Type := fun _ => ProofImpl.type

namespace Proof

private theorem typeDef : Proof ω = ProofImpl.type :=
  by unfold Proof ; rfl

private def toImpl : Proof ω → ProofImpl.type :=
  by rw [typeDef] ; exact id

private def ofImpl : ProofImpl.type → Proof ω :=
  by rw [typeDef] ; exact id

instance instNonemptyProof : Nonempty (Proof ω) :=
  by rw [typeDef] ; exact ProofImpl.property

/-- The null proof. -/
extern_def null' as "null" : Unit → Proof ω
@[inherit_doc null']
def null : Env ω (Proof ω) := pure <| null' ()

instance : Inhabited (Proof ω) := ⟨null' ()⟩

end Proof



/-! ## User-facing definitions -/



/-! ### `Srt` functions -/

extern_env_defs [ω] in "termManager"

  /-- Get the Boolean sort. -/
  def getBooleanSort : Srt ω

  /-- Get the Integer sort. -/
  def getIntegerSort : Srt ω

  /-- Get the Real sort. -/
  def getRealSort : Srt ω

  /-- Get the regular expression sort. -/
  def getRegExpSort : Srt ω

  /-- Get the rounding mode sort. -/
  def getRoundingModeSort : Srt ω

  /-- Get the string sort. -/
  def getStringSort : Srt ω

  /-- Create an array sort.

  - `indexSort` The array index sort.
  - `elemSort` The array element sort.
  -/
  def? mkArraySort : (indexSort elemSort : Srt ω) → Srt ω

  /-- Create a bit-vector sort.

  - `size` The bit-width of the bit-vector sort.
  -/
  def? mkBitVectorSort : (size : UInt32) → Srt ω

  /-- Create a floating-point sort.

  - `exp` The bit-width of the exponent of the floating-point sort.
  - `sig` The bit-width of the significand of the floating-point sort.
  -/
  def? mkFloatingPointSort : (exp sig : UInt32) → Srt ω

  /-- Create a finite-field sort from a given string of base n.

  - `size` The modulus of the field. Must be a prime.
  -/
  private def? mkFiniteFieldSortFromString :
    (size : String) → (base : UInt32 := 10) → Srt ω

@[inherit_doc mkFiniteFieldSortFromString]
abbrev mkFiniteFieldSort (size : Nat) : Env ω (Srt ω) :=
  mkFiniteFieldSortFromString (toString size) 10
@[inherit_doc mkFiniteFieldSortFromString]
abbrev mkFiniteFieldSort? (size : Nat) : Env ω (Option (Srt ω)) := do
  try some <$> mkFiniteFieldSort size catch _ => return none

extern_env_defs [ω] in "termManager"

  /-- Create function sort.

  - `sorts` The sort of the function arguments.
  - `codomain` The sort of the function return value.
  -/
  def? mkFunctionSort : (sorts : Array (Srt ω)) → (codomain : Srt ω) → Srt ω

  /-- Create a predicate sort.

  This is equivalent to calling `mkFunctionSort` with Boolean sort as the codomain.

  - `sorts` The list of sorts of the predicate.
  -/
  def? mkPredicateSort : (sorts : Array (Srt ω)) → Srt ω

  /-- Create a tuple sort.

  - `sorts` The sorts of the elements of the tuple.
  -/
  def? mkTupleSort : (sorts : Array (Srt ω)) → Srt ω

  /-- Create an uninterpreted sort constructor sort.

  An uninterpreted sort constructor is an uninterpreted sort with arity > 0.

  - `arity` The arity of the sort (must be > 0).
  - `symbol` The symbol of the sort.
  -/
  def? mkUninterpretedSortConstructorSort : (arity : Nat) → (symbol : String) → Srt ω

  /-- Create a set parameter.

  - `elemSort` The sort of the set elements.
  -/
  def? mkSetSort : (sort : Srt ω) → Srt ω

  /-- Create a set parameter.

  - `elemSort` The sort of the set elements.
  -/
  def? mkBagSort : (sort : Srt ω) → Srt ω

  /-- Create a set parameter.

  - `elemSort` The sort of the set elements.
  -/
  def? mkSequenceSort : (sort : Srt ω) → Srt ω

  /-- Create an abstract sort. An abstract sort represents a sort for a given kind whose parameters
  and arguments are unspecified.

  The kind `k` must be the kind of a sort that can be abstracted, *i.e.* a sort that has indices or
  arguments sorts. For example, `SortKind.ARRAY_SORT` and `SortKind.BITVECTOR_SORT` can be passed as
  the kind `k` to this function, while `SortKind.INTEGER_SORT` and `SortKind.STRING_SORT` cannot.

  **NB:** Providing the kind `SortKind.ABSTRACT_SORT` as an argument to this function returns the
  (fully) unspecified sort, denoted `?`.

  **NB:** Providing a kind `k` that has no indices and a fixed arity of argument sorts will return
  the sort of kind `k` whose arguments are the unspecified sort. For example, `mkAbstractSort
  SortKind.ARRAY_SORT` will return the sort `(ARRAY_SORT ? ?)` instead of the abstract sort whose
  abstract kind is `SortKind.ARRAY_SORT`.
  -/
  def? mkAbstractSort : (k : SortKind) → Srt ω

  /-- Create an uninterpreted sort.

  - `symbol` The name of the sort.
  -/
  def mkUninterpretedSort : (symbol : String) → Srt ω

  /-- Create a nullable sort.

  - `sort` The sort of the element of the nullable.
  -/
  def? mkNullableSort : (sort : Srt ω) → Srt ω

  /-- Create a sort parameter.

  - `symbol` The name of the sort.

  **Warning**: This function is experimental and may change in future versions.
  -/
  def mkParamSort : (symbol : String) → Srt ω



namespace Srt

@[inherit_doc getBooleanSort]
abbrev mkBoolean := @getBooleanSort

@[inherit_doc getBooleanSort]
abbrev mkInteger := @getIntegerSort

@[inherit_doc getBooleanSort]
abbrev mkReal := @getRealSort

/-- Get the kind of this sort. -/
extern_def getKind : Srt ω → SortKind

/-- Determine if this is the null sort. -/
extern_def isNull : Srt ω → Bool

/-- Determine if this is the Boolean sort (SMT-LIB: `Bool`). -/
extern_def isBoolean : Srt ω → Bool

/-- Determine if this is the Integer sort (SMT-LIB: `Int`). -/
extern_def isInteger : Srt ω → Bool

/-- Determine if this is the Real sort (SMT-LIB: `Real`). -/
extern_def isReal : Srt ω → Bool

/-- Determine if this is the String sort (SMT-LIB: `String`). -/
extern_def isString : Srt ω → Bool

/-- Determine if this is the regular expression sort (SMT-LIB: `RegLan`). -/
extern_def isRegExp : Srt ω → Bool

/-- Determine if this is the rounding mode sort (SMT-LIB: `RoundingMode`). -/
extern_def isRoundingMode : Srt ω → Bool

/-- Determine if this is a bit-vector sort (SMT-LIB: `(_ BitVec i)`). -/
extern_def isBitVector : Srt ω → Bool

/-- Determine if this is a floating-point sort (SMT-LIB: `(_ FloatingPoint eb sb)`). -/
extern_def isFloatingPoint : Srt ω → Bool

/-- Determine if this is a datatype sort. -/
extern_def isDatatype : Srt ω → Bool

/-- Determine if this is a datatype constructor sort. -/
extern_def isDatatypeConstructor : Srt ω → Bool

/-- Determine if this is a datatype selector sort. -/
extern_def isDatatypeSelector : Srt ω → Bool

/-- Determine if this is a datatype tester sort. -/
extern_def isDatatypeTester : Srt ω → Bool

/-- Determine if this is a datatype updater sort. -/
extern_def isDatatypeUpdater : Srt ω → Bool

/-- Determine if this is a function sort. -/
extern_def isFunction : Srt ω → Bool

/-- Determine if this is a predicate sort.

A predicate sort is a function sort that maps to the Boolean sort. All predicate sorts are also
function sorts.
-/
extern_def isPredicate : Srt ω → Bool

/-- Determine if this is a tuple sort. -/
extern_def isTuple : Srt ω → Bool

/-- Determine if this is a nullable sort. -/
extern_def isNullable : Srt ω → Bool

/-- Determine if this is a record sort.

**Warning**: this function is experimental and may change in future versions.
-/
extern_def isRecord : Srt ω → Bool

/-- Determine if this is an array sort. -/
extern_def isArray : Srt ω → Bool

/-- Determine if this is a finite field sort. -/
extern_def isFiniteField : Srt ω → Bool

/-- Determine if this is a Set sort. -/
extern_def isSet : Srt ω → Bool

/-- Determine if this is a Bag sort. -/
extern_def isBag : Srt ω → Bool

/-- Determine if this is a Sequence sort. -/
extern_def isSequence : Srt ω → Bool

/-- Determine if this is an abstract sort. -/
extern_def isAbstract : Srt ω → Bool

/-- Determine if this is an uninterpreted sort. -/
extern_def isUninterpretedSort : Srt ω → Bool

/-- Determine if this is an uninterpreted sort constructor.

An uninterpreted sort constructor has arity `> 0` and can be instantiated to construct uninterpreted
sorts with given sort parameters.
-/
extern_def isUninterpretedSortConstructor : Srt ω → Bool

/-- Determine if this is an instantiated (parametric datatype or uninterpreted sort constructor)
sort.

An instantiated sort is a sort that has been constructed from instantiating a sort with sort
arguments --- see also `cvc5.Sort.instantiate`.
-/
extern_def isInstantiated : Srt ω → Bool

/-- Determine if this term has a symbol (a name).

For example, free constants and variables have symbols.
-/
extern_def!? hasSymbol : Srt ω → Except Error Bool

/-- Get the symbol of this sort.

The symbol of this sort is the string that was provided when constructing it *via* one of
`Solver.mkUninterpretedSort`, `Solver.mkUnresolvedSort`, or
`Solver.mkUninterpretedSortConstructorSort`.
-/
extern_def!? getSymbol : Srt ω → Except Error String

/-- The arity of a function sort. -/
extern_def!? getFunctionArity : Srt ω → Except Error Nat

/-- The domain sorts of a function sort. -/
extern_def!? getFunctionDomainSorts : Srt ω → Except Error (Array (Srt ω))

/-- The codomain sort of a function sort. -/
extern_def!? getFunctionCodomainSort : Srt ω → Except Error (Srt ω)

/-- The array index sort of an array index. -/
extern_def!? getArrayIndexSort : Srt ω → Except Error (Srt ω)

/-- The array element sort of an array index. -/
extern_def!? getArrayElementSort : Srt ω → Except Error (Srt ω)

/-- The element sort of a set sort. -/
extern_def!? getSetElementSort : Srt ω → Except Error (Srt ω)

/-- The element sort of a bag sort. -/
extern_def!? getBagElementSort : Srt ω → Except Error (Srt ω)

/-- The element sort of a sequence sort. -/
extern_def!? getSequenceElementSort : Srt ω → Except Error (Srt ω)

/-- The sort kind of an abstract sort, which denotes the kind of sorts that this abstract sort
denotes.
-/
extern_def!? getAbstractedKind : Srt ω → Except Error SortKind

/-- The arity of an uninterpreted sort constructor sort. -/
extern_def!? getUninterpretedSortConstructorArity : Srt ω → Except Error UInt32

/-- The bit-width of the bit-vector sort. -/
extern_def!? getBitVectorSize : Srt ω → Except Error UInt32

/-- The size of the finite field sort. -/
extern_def!? getFiniteFieldSize : Srt ω → Except Error Nat

/-- The bit-width of the exponent of the floating-point sort. -/
extern_def!? getFloatingPointExponentSize : Srt ω → Except Error UInt32

/-- The width of the significand of the floating-point sort. -/
extern_def!? getFloatingPointSignificandSize : Srt ω → Except Error UInt32

/-- The length of a tuple sort. -/
extern_def!? getTupleLength : Srt ω → Except Error UInt32

/-- The element sorts of a tuple sort. -/
extern_def!? getTupleSorts : Srt ω → Except Error (Array (Srt ω))

/-- The element sort of a nullable sort. -/
extern_def!? getNullableElementSort : Srt ω → Except Error (Srt ω)

/-- Get the associated uninterpreted sort constructor of an instantiated uninterpreted sort. -/
extern_def!? getUninterpretedSortConstructor : Srt ω → Except Error (Srt ω)

/-- Instantiate a parameterized datatype sort or uninterpreted sort constructor sort.

Create sort parameters with `TermManager.mkParamSort symbol`.

- `params` The list of sort parameters to instantiate with.
-/
extern_def!? instantiate : Srt ω → (params : Array (Srt ω)) → Except Error (Srt ω)

/-- Simultaneous substitution of Sorts.

Note that this replacement is applied during a pre-order traversal and only once to the sort. It is not run until fix point. In the case that `sorts` contains duplicates, the replacement earliest in
the vector takes priority.

**Warning:** This function is experimental and may change in future versions.

- `sorts` The sub-sorts to be substituted within this sort.
- `replacements` The sort replacing the substituted sub-sorts.
-/
extern_def!? substitute
: Srt ω → (sorts : Array (Srt ω)) → (replacements : Array (Srt ω)) → Except Error (Srt ω)

end Srt



namespace Op

/-- Syntactic equality operator. -/
protected extern_def beq : Op ω → Op ω → Bool

instance : BEq (Op ω) := ⟨Op.beq⟩

/-- Get the kind of this operator. -/
extern_def getKind : Op ω → Kind

/-- Determine if this operator is indexed. -/
extern_def isIndexed : Op ω → Bool

/-- Get the number of indices of this operator. -/
extern_def getNumIndices : Op ω → Nat

/-- Get the index at position `i` of an indexed operator. -/
protected extern_def get : (op : Op ω) → Fin op.getNumIndices → Term ω

instance : GetElem (Op ω) Nat (Term ω) fun op i => i < op.getNumIndices where
  getElem op i h := op.get ⟨i, h⟩



extern_env_defs [ω] in "termManager"

  /-- Create operator of kind:

  - `Kind.DIVISIBLE` (to support arbitrary precision integers)

  See `cvc5.Kind` for a description of the parameters.

  - `kind` The kind of the operator.
  - `arg` The string argument to this operator.
  -/
  def? ofString as "mkOpOfString" : (kind : Kind) → (arg : String) → Op ω

  /-- Create n-ary term of given kind from a given operator.

  Create operators with `mkOp`.

  - `op` The operator.
  - `children` The children of the term.
  -/
  def? mkTerm as "mkTermOfOp" : (op : Op ω) → (children : Array (Term ω) := #[]) → Term ω

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
  `Term.mk` directly without creating an `Op` first.
  -/
  def? ofIndices as "mkOpOfIndices" : (kind : Kind) → (args : Array Nat := #[]) → Op ω

@[inherit_doc ofIndices]
abbrev ofOp := @ofIndices

end Op

/-- Create n-ary term of given kind.

- `kind` The kind of the term.
- `children` The children of the term.
-/
extern_env_def? [ω] in "termManager" mkTerm :
  (kind : Kind) → (children : Array (Term ω) := #[]) → Term ω

namespace Term

@[inherit_doc cvc5.mkTerm]
def mk := @cvc5.mkTerm

@[inherit_doc Op.mkTerm]
def ofOp := @Op.mkTerm

extern_env_defs [ω] in "termManager"

  /-- Create n-ary term of given kind.

  - `kind` The kind of the term.
  - `term` The head of the children list.
  - `tail` The tail of the children list.
  -/
  def? mkInto as "mkTermInto" :
    (kind : Kind) → (term : Term ω) → (children : Array (Term ω) := #[]) → Term ω

  /-- Create a free constant.

  Note that the returned term is always fresh, even if the same arguments were provided on a
  previous call to `mkConst`.

  - `sort` The sort of the constant.
  - `symbol` The name of the constant (optional).
  -/
  def mkConst : (sort : Srt ω) → (symbol : String) → Term ω

  /--
  Create a bound variable to be used in a binder (i.e., a quantifier, a lambda, or a witness
  binder).

  The returned term is always fresh, even if the same arguments were provided on a previous call to
  mkConst().

  - `sort`: the sort of the variable.
  - `symbol`: the name of the variable (optional).
  -/
  def mkVar : (sort : Srt ω) → (symbol : String) → Term ω

  /-- Create a Boolean constant.

  - `b`: The Boolean constant.
  -/
  def mkBoolean : (b : Bool) → Term ω

  /-- Create an integer-value term.

  - `s`: the string representation of the constant, may represent an integer such as (`"123"`).
  -/
  private def? mkIntegerFromString : (s : String) → Term ω

  /-- Create a real-value term.

  - `s`: the string representation of the constant, may represent an integer (`"123"`) or a real
    constant (`"12.34"`, `"12/34"`).
  -/
  private def? mkRealFromString : (s : String) → Term ω

/-- Create an integer-value term. -/
def mkInteger : Int → Env ω (Term ω) := mkIntegerFromString ∘ toString

/-- Create a real-value term from a `Std.Internal.Rat`. -/
def mkRealOfRat (rat : Std.Internal.Rat) : Env ω (Term ω) :=
  mkRealFromString s!"{rat.num}/{rat.den}"

/-- Create a real-value term from numerator/denominator `Int`-s. -/
def mkReal (num : Int) (den : Int := 1)
  (den_ne_0 : den ≠ 0 := by simp <;> omega)
: Env ω (Term ω) :=
  let (num, den) :=
    match h : den with
    | .ofNat 0 => by contradiction
    | .ofNat den => (num, den)
    | .negSucc denMinus1 => (-num, denMinus1.succ)
  mkRealOfRat <| Std.Internal.mkRat num den

/-- Get the kind of this term. -/
extern_def getKind : Term ω → Kind

/-- Get the sort of this term. -/
extern_def getSort : Term ω → Srt ω

/-- Determine if this term has an operator. -/
extern_def hasOp : Term ω → Bool

/-- Determine if this term has a symbol (a name).

For example, free constants and variables have symbols.
-/
extern_def hasSymbol : Term ω → Bool

/-- Get the id of this term. -/
extern_def getId : Term ω → Nat

/-- Get the number of children of this term. -/
extern_def getNumChildren : Term ω → Nat

/-- Is this term a skolem? -/
extern_def isSkolem : Term ω → Bool

/-- Get the child term of this term at a given index. -/
protected extern_def get : (t : Term ω) → Fin t.getNumChildren → Term ω

/-- Get the operator of a term with an operator.

Requires that this term has an operator (see `hasOp`).
-/
extern_def!? getOp : Term ω → Except Error (Op ω)

/-- Get the value of a Boolean term as a native Boolean value.

Requires `term` to have sort Bool.
-/
extern_def!? getBooleanValue : Term ω → Except Error Bool

/-- Get the string representation of a bit-vector value.

Requires `term` to have a bit-vector sort.

- `base`: `2` for binary, `10` for decimal, and `16` for hexadecimal.
-/
extern_def!? getBitVectorValue : Term ω → UInt32 → Except Error String

/-- Get the native integral value of an integral value. -/
extern_def!? getIntegerValue : Term ω → Except Error Int

/-- Get the native rational value of a real, rational-compatible value. -/
extern_def!? getRationalValue : Term ω → Except Error Std.Internal.Rat

/-- Get the symbol of this term.

Requires that this term has a symbol (see `hasSymbol`).

The symbol of the term is the string that was provided when constructing it *via*
`TermManager.mkConst` or `TermManager.mkVar`.
-/
extern_def!? getSymbol : Term ω → Except Error String

/-- Get skolem identifier of this term.

Requires `isSkolem`.
-/
extern_def!? getSkolemId : (Term ω) → Except Error SkolemId

/-- Get the skolem indices of this term.

Requires `isSkolem`.

Returns the skolem indices of this term. This is a list of terms that the skolem function is indexed
by. For example, the array diff skolem `SkolemId.ARRAY_DEQ_DIFF` is indexed by two arrays.
-/
extern_def!? getSkolemIndices : Term ω → Except Error (Array (Term ω))

instance : GetElem (Term ω) Nat (Term ω) fun t i => i < t.getNumChildren where
  getElem t i h := t.get ⟨i, h⟩

protected def forIn {β : Type u} [Monad m]
  (t : Term ω) (b : β) (f : Term ω → β → m (ForInStep β))
: m β :=
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

instance : ForIn m (Term ω) (Term ω) where
  forIn := Term.forIn

/-- Get the children of a term. -/
def getChildren (t : Term ω) : Array (Term ω) := Id.run do
  let mut cts := #[]
  for ct in t do
    cts := cts.push ct
  cts

/-- Boolean negation. -/
protected extern_def!? not : (t : Term ω) → Except Error (Term ω)

/-- Boolean and. -/
protected extern_def!? and : (lft rgt : Term ω) → Except Error (Term ω)

/-- Boolean or. -/
protected extern_def!? or : (lft rgt : Term ω) → Except Error (Term ω)

/-- Boolean exclusive or. -/
protected extern_def!? xor : (lft rgt : Term ω) → Except Error (Term ω)

/-- Equality. -/
protected extern_def!? eq : (lft rgt : Term ω) → Except Error (Term ω)

/-- Boolean implication. -/
protected extern_def!? imp : (lft rgt : Term ω) → Except Error (Term ω)

/-- If-then-else.

- `cnd`: condition, must be a Boolean term;
- `thn`: then-branch of some sort `S`;
- `els`: else-branch of *the same* sort `S`.
-/
protected extern_def!? ite : (cnd thn els : Term ω) → Except Error (Term ω)

end Term



namespace Proof

/-- Get the proof rule used by the root step of the root. -/
extern_def getRule : Proof ω → ProofRule

/-- Get the proof rewrite rule used by the root step of the proof.

Requires that `getRule` does not return `ProofRule.DSL_REWRITE` or `ProofRule.REWRITE`.
-/
extern_def!? getRewriteRule : Proof ω → Except Error ProofRewriteRule

/-- The conclusion of the root step of the proof. -/
extern_def getResult : Proof ω → Term ω

/-- The premises of the root step of the proof. -/
extern_def getChildren : Proof ω → Array (Proof ω)

/-- The arguments of the root step of the proof as a vector of terms.

Some of those terms might be strings.
-/
extern_def getArguments : Proof ω → Array (Term ω)

/-- Operator overloading for referential equality of two proofs. -/
protected extern_def beq : Proof ω → Proof ω → Bool

instance : BEq (Proof ω) := ⟨Proof.beq⟩

/-- Hash function for proofs. -/
protected extern_def hash : Proof ω → UInt64

instance : Hashable (Proof ω) := ⟨Proof.hash⟩

end Proof



namespace Solver variable (solver : Solver ω)

/-- Get a string representation of the version of this solver. -/
extern_def getVersion (solver : Solver ω) : Env ω String

/-- Simplify a term or formula based on rewriting and (optionally) applying substitutions for
solved variables.

If `applySubs` is true, then for example, if `(= x 0)` was asserted to this solver, this function
may replace occurrences of `x` with `0`.

- `t` The term to simplify.
- `applySubs` True to apply substitutions for solved variables.
-/
extern_def simplify :
  (solver : Solver ω) → (term : Term ω) → (applySubs : Bool := false) → Env ω (Term ω)

/-- Set option.

- `option`: The option name.
- `value`: The option value.
-/
extern_def setOption (solver : Solver ω) (option value : String) : Env ω Unit

/-- Remove all assertions. -/
extern_def resetAssertions (solver : Solver ω) : Env ω Unit

/-- Set logic.

- `logic`: The logic to set.
-/
extern_def setLogic (solver : Solver ω) (logic : String) : Env ω Unit

/-- Declare n-ary function symbol.

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
extern_def declareFun (solver : Solver ω)
  (symbol : String) (sorts : Array (Srt ω)) (sort : Srt ω) (fresh : Bool := false)
: Env ω (Term ω)

/-- Assert a formula.

- `term`: The formula to assert.
-/
extern_def assertFormula : (solver : Solver ω) → (term : Term ω) → Env ω Unit

/-- Check satisfiability. -/
extern_def checkSat : (solver : Solver ω) → Env ω Result

/-- Check satisfiability assuming the given formulas.

- `assumptions`: The formulas to assume.
-/
extern_def checkSatAssuming : (solver : Solver ω) → (assumptions : Array (Term ω)) → Env ω Result

/-- Get a proof associated with the most recent call to `checkSat`.

Requires to enable option `produce-proofs`.
-/
extern_def getProof : (solver : Solver ω) → Env ω (Array (Proof ω))

/--
Get the values of the given term in the current model.

SMT-LIB:

\verbatim embed:rst:leading-asterisk
.. code:: smtlib

    (get-value ( <term>* ))
\endverbatim

- `terms`: The term for which the value is queried.
-/
extern_def getValue (solver : Solver ω) (term : Term ω) : Env ω (Term ω)

/--
Get the values of the given terms in the current model.

SMT-LIB:

\verbatim embed:rst:leading-asterisk
.. code:: smtlib

    (get-value ( <term>* ))
\endverbatim

- `terms`: The terms for which the values are queried.
-/
extern_def getValues (solver : Solver ω) (terms : Array (Term ω)) : Env ω (Array (Term ω))

/-- Prints a proof as a string in a selected proof format mode.

Other aspects of printing are taken from the solver options.

- `proof`: A proof, usually obtained from `getProof`.
-/
extern_def proofToString (solver : Solver ω) : (proof : Proof ω) → Env ω String

-- /-- Parse a string containing SMT-LIB commands.

-- Commands that produce a result such as `(check-sat)`, `(get-model)`, ... are executed but the
-- results are ignored.
-- -/
-- extern_def parseCommands (solver : Solver ω) : (smtLib : String) → Env ω Unit

end Solver
