import Lean.Server.Utils

import cvc5

namespace cvc5

namespace Test

/-! ## A few sanity tests -/

example [Monad m] : MonadLiftT m (EnvT m) := inferInstance
example : MonadLift IO Env := inferInstance
example : MonadLift BaseIO Env := inferInstance

/-! ## Helpers for the rest of the tests -/

def IO.run : IO Unit → IO Unit :=
  id

def fail {α : outParam Type} (msg : String) : IO α :=
  IO.throwServerError msg

protected def pref (hint : String) : String :=
  if hint.isEmpty then "" else "[" ++ hint ++ "] "

def assertEq [ToString α] [BEq α] (lft rgt : α) (hint := "") : IO Unit := do
  if lft != rgt then
    IO.eprintln s!"{Test.pref hint}comparison failed: `{lft}` is different from `{rgt}`"
    fail "assertion failed"

def assertTrue (b : Bool) (hint := "") : IO Unit :=
  assertEq true b hint

def assertFalse (b : Bool) (hint := "") : IO Unit :=
  assertEq false b hint

def assertNone [ToString α] (a? : Option α) (hint := "") : IO Unit := do
  if let some a := a? then
    IO.eprintln s!"{Test.pref hint}expected none, got {a}"
    fail "assertion failed"

def assertSome (a? : Option α) (hint := "") : IO α := do
  let some a := a?
    | IO.eprintln s!"{Test.pref hint}expected non-none value, got none"
      fail "assertion failed"
  return a

def assertSomeDiscard (a? : Option α) (hint := "") : IO Unit := do
  let _ ← assertSome a? (hint := hint)

def assertNe [ToString α] [BEq α] (lft rgt : α) (hint := "") : IO Unit := do
  if lft == rgt then
    IO.eprintln s!"{Test.pref hint}comparison failed: `{lft}` is the same as `{rgt}`"
    fail "assertion failed"

def assertOk
  (code : Env α)
  (hint : String := "")
: Env α := do
  try code catch e =>
    IO.eprintln s!"{Test.pref hint}expected `.ok` result, got `{e}`"
    fail "assertion failed"

def assertOkDiscard
  (result : Env α)
  (hint : String := "")
: Env Unit := do
  let _ ← assertOk result hint
  return ()

def assertAnyError
  (expected : String)
  (code : Env α)
  (errorDo : Error → Env Unit := fun _ => return ())
  (hint : String := "")
: Env Unit := do
  try
    let _ ← code
    IO.eprintln s!"{Test.pref hint}expected {expected}, got `.ok` result"
    fail "assertion failed"
  catch e => errorDo e

def assertError
  (expected : String)
  (code : Env α)
  (hint : String := "")
: Env Unit :=
  assertAnyError expected
    code
    (hint := hint)
    fun
    | .error err => do
      if err.trimAscii == expected.trimAscii then
        return ()
      else
        IO.eprintln s!"{Test.pref hint}expected cvc5 error `{expected}`, got cvc5 error `{err}`"
        fail "test failed"
    | .recoverable err => do
        IO.eprintln s!"{Test.pref hint}expected error `{expected}`, got recoverable error `{err}`"
        fail "test failed"
    | .unsupported err => do
        IO.eprintln s!"{Test.pref hint}expected error `{expected}`, got unsupported error `{err}`"
        fail "test failed"
    | .option err => do
        IO.eprintln s!"{Test.pref hint}expected error `{expected}`, got option error `{err}`"
        fail "test failed"
    | .missingValue => do
        IO.eprintln s!"{Test.pref hint}expected cvc5 error `{expected}`, got missing value error"
        fail "test failed"

end Test

namespace Result

def toOption (res : Result) : Option Bool :=
  if res.isSat then true
  else if res.isUnsat then false
  else none

end Result

namespace Solver variable (solver : Solver)

variable [Monad m]

def checkSat? : Env (Option Bool) :=
  Result.toOption <$> solver.checkSat

def checkSatAssuming? (terms : Array Term) : Env (Option Bool) :=
  Result.toOption <$> solver.checkSatAssuming terms

end Solver

namespace Test

scoped syntax
  docComment ?
  "test! " ("[" declId ", " declId "] ")? (ident (ident)? " => ")? term : command
scoped syntax
  docComment ?
  "test? " ("[" declId ", " declId "] ")? (ident (ident)? " => ")? term : command

macro_rules
| `(command|
  $[ $outputComment:docComment ]?
  test! $[ [ $fileId:ident , $testId:ident ] ]?
    $[$tmIdent?:ident $[$solverIdent?:ident]? =>]?
    $code:term
) => do
  let errPrefStrLit :=
    match (fileId, testId) with
    | (some fileId, some testId) =>
      Lean.Syntax.mkStrLit s!"[{fileId}.{testId}] test failed:\n"
    | _ => Lean.Syntax.mkStrLit "test failed"
  let runFun ← `(term| cvc5.Env.run)
  let toRun ←
    if let some tmIdent := tmIdent? then
      let boolIdent := `bool |> Lean.mkIdent
      let intIdent := `int |> Lean.mkIdent
      let realIdent := `real |> Lean.mkIdent
      let uninterpretedIdent := `uninterpreted |> Lean.mkIdent
      if let some (some solverIdent) := solverIdent? then
        `(do
            let $tmIdent:ident ← TermManager.new
            let $solverIdent:ident ← Solver.new $tmIdent
            let $boolIdent ← $tmIdent:ident |>.getBooleanSort
            let $intIdent ← $tmIdent:ident |>.getIntegerSort
            let $realIdent ← $tmIdent:ident |>.getRealSort
            let $uninterpretedIdent ← $tmIdent:ident |>.mkUninterpretedSort "u"
            $code:term
        )
      else
        `(do
            let $tmIdent:ident ← TermManager.new
            $code:term
        )
    else `(do $code:term)

  `(
    $[ $outputComment:docComment ]?
    #guard_msgs in #eval IO.run do
      let res ← $runFun:term $toRun
      match res with
      | .ok res => return res
      | .error e =>
        IO.eprintln ($errPrefStrLit ++ (toString e))
        return default
  )
| `(command|
  $[ $_outputComment:docComment ]?
  test? $[ [ $fileId:ident, $testId:ident ] ]? $[$tmIdent?:ident =>]? $code:term
) => do
  let errPrefStrLit :=
    match (fileId, testId) with
    | (some fileId, some testId) =>
      Lean.Syntax.mkStrLit s!"[{fileId}.{testId}] test failed:\n"
    | _ => Lean.Syntax.mkStrLit "test failed"
  let runFun ← `(term| cvc5.Env.run)
  let mut code ←
    if let some tmIdent := tmIdent? then
      `(doSeq|
        let $tmIdent:ident ← TermManager.new
        $code:term
      )
    else `(doSeq| $code:term)

  `(
    #eval IO.run do
      let res ← $runFun:term do $code
      match res with
      | .ok res => return res
      | .error e =>
        IO.eprintln ($errPrefStrLit ++ (toString e))
        return default
  )

end Test

end cvc5
