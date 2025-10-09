import Lean.Server.Utils

import cvc5

namespace cvc5

namespace Test

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
      if err = expected then
        return ()
      else
        IO.eprintln s!"{Test.pref hint}expected cvc5 error `{expected}`, got cvc5 error `{err}`"
        fail "assertion failed"
    | .recoverable err => do
        IO.eprintln s!"{Test.pref hint}expected error `{expected}`, got recoverable error `{err}`"
        fail "assertion failed"
    | .unsupported err => do
        IO.eprintln s!"{Test.pref hint}expected error `{expected}`, got unsupported error `{err}`"
        fail "assertion failed"
    | .option err => do
        IO.eprintln s!"{Test.pref hint}expected error `{expected}`, got option error `{err}`"
        fail "assertion failed"
    | .missingValue => do
        IO.eprintln s!"{Test.pref hint}expected cvc5 error `{expected}`, got missing value error"
        fail "assertion failed"

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
  "test! " ("[" declId ", " declId "] ")? (ident " => ")? term : command
scoped syntax
  docComment ?
  "test? " ("[" declId ", " declId "] ")? (ident " => ")? term : command

macro_rules
| `(command|
  $[ $outputComment:docComment ]?
  test! $[ [ $fileId:ident , $testId:ident ] ]? $[$solverIdent?:ident =>]? $code:term
) => do
  let errPrefStrLit :=
    match (fileId, testId) with
    | (some fileId, some testId) =>
      Lean.Syntax.mkStrLit s!"[{fileId}.{testId}] test failed:\n"
    | _ => Lean.Syntax.mkStrLit "test failed"
  let runFun ← `(term| cvc5.Env.run)
  let toRun ←
    if let some solverIdent := solverIdent? then
      `(do
          let $solverIdent:ident ← Solver.mk
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
  test? $[ [ $fileId:ident, $testId:ident ] ]? $[$solverIdent?:ident =>]? $code:term
) => do
  let errPrefStrLit :=
    match (fileId, testId) with
    | (some fileId, some testId) =>
      Lean.Syntax.mkStrLit s!"[{fileId}.{testId}] test failed:\n"
    | _ => Lean.Syntax.mkStrLit "test failed"
  let runFun ← `(term| cvc5.Env.run)
  let mut code ←
    if let some solverIdent := solverIdent? then
      `(doSeq|
        let $solverIdent:ident ← Solver.mk
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
