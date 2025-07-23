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
  (code : Env ω α)
  (hint : String := "")
: Env ω α := do
  try code catch e =>
    IO.eprintln s!"{Test.pref hint}expected `.ok` result, got `{e}`"
    fail "assertion failed"

def assertOkDiscard
  (result : Env ω α)
  (hint : String := "")
: Env ω Unit := do
  let _ ← assertOk result hint
  return ()

def assertAnyError
  (expected : String)
  (errorDo : Error → Env ω Unit)
  (result : Env ω α)
  (hint : String := "")
: Env ω Unit := do
  try
    let _res ← result
    IO.eprintln s!"{Test.pref hint}expected {expected}, got `.ok` result"
    fail "assertion failed"
  catch e => errorDo e

def assertError
  (expected : String)
  (result : Env ω α)
  (hint : String := "")
: Env ω Unit :=
  assertAnyError s!"cvc5 error `{expected}`"
    (fun
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
    | .parsing err => do
        IO.eprintln s!"{Test.pref hint}expected cvc5 error `{expected}`, got parsing error `{err}`"
        fail "assertion failed"
    | .missingValue => do
        IO.eprintln s!"{Test.pref hint}expected cvc5 error `{expected}`, got missing value error"
        fail "assertion failed"
    )
    result hint

end Test

namespace Result

def toOption (res : Result) : Option Bool :=
  if res.isSat then true
  else if res.isUnsat then false
  else none

end Result

namespace Solver variable (solver : Solver ω)

def checkSat? : Env ω (Option Bool) :=
  Result.toOption <$> solver.checkSat

def checkSatAssuming? (terms : Array (Term ω)) : Env ω (Option Bool) :=
  Result.toOption <$> solver.checkSatAssuming terms

end Solver

namespace Test

scoped syntax
  docComment ?
  "test! " ("[" declId ", " declId "] ")? ("smt ")? (ident " => ")? term : command
scoped syntax
  docComment ?
  "test? " ("[" declId ", " declId "] ")? ("smt ")? (ident " => ")? term : command

macro_rules
| `(command|
  $[ $outputComment:docComment ]?
  test! $[ [ $fileId:ident , $testId:ident ] ]? $code:term
) => do
  let errPrefStrLit :=
    match (fileId, testId) with
    | (some fileId, some testId) =>
      Lean.Syntax.mkStrLit s!"[{fileId}.{testId}] test failed:\n"
    | _ => Lean.Syntax.mkStrLit "test failed "
  `(
    $[ $outputComment:docComment ]?
    #guard_msgs in #eval cvc5.runIO do
      try ($code) catch e =>
        IO.eprintln ($errPrefStrLit ++ (toString e))
        return default
  )
| `(command| $[$outputComment]? test? $[ [ $fileId, $testId ] ]? $code:term) => `(
  $[$outputComment]?
  test? $[ [ $fileId, $testId ] ]? _tm => $code
)

end Test
