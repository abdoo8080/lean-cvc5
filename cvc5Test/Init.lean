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
  (code : SolverM α)
  (hint : String := "")
: SolverM α := fun solver => do
  match ← code solver with
  | (.ok res, solver) => return (.ok res, solver)
  | (.error e, _) =>
    IO.eprintln s!"{Test.pref hint}expected `.ok` result, got `{e}`"
    fail "assertion failed"

def assertOkDiscard
  (result : SolverM α)
  (hint : String := "")
: SolverM Unit := do
  let _ ← assertOk result hint
  return ()

def assertAnyError
  (expected : String)
  (errorDo : Error → SolverM Unit)
  (result : SolverM α)
  (hint : String := "")
: SolverM Unit := fun solver => do
  match ← result solver with
  | (.ok _, _) =>
    IO.eprintln s!"{Test.pref hint}expected {expected}, got `.ok` result"
    fail "assertion failed"
  | (.error e, solver) => errorDo e solver

def assertError
  (expected : String)
  (result : SolverM α)
  (hint : String := "")
: SolverM Unit :=
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

namespace Solver

variable [Monad m]

def checkSat? : SolverT m (Option Bool) :=
  Result.toOption <$> Solver.checkSat

def checkSatAssuming? (terms : Array Term) : SolverT m (Option Bool) :=
  Result.toOption <$> Solver.checkSatAssuming terms

def runWith! [Inhabited α] (tm : TermManager) (query : SolverM α) : IO α := do
  match ← Solver.run tm query with
  | .ok res => return res
  | .error err =>
    IO.eprintln err.toString
    return default

def runIO! [Inhabited α] (query : SolverM α) : IO α := do
  match ← Solver.run (← TermManager.new) query with
  | .ok res => return res
  | .error err =>
    IO.eprintln err.toString
    return default

end Solver

def SolverT.run! [Inhabited α] (query : SolverT IO α) := Solver.runIO! query

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
  test! $[ [ $fileId:ident , $testId:ident ] ]? $tm:ident => $code:term
) => do
  let errPrefStrLit :=
    match (fileId, testId) with
    | (some fileId, some testId) =>
      Lean.Syntax.mkStrLit s!"[{fileId}.{testId}] test failed:\n"
    | _ => Lean.Syntax.mkStrLit "test failed"
  `(
    $[ $outputComment:docComment ]?
    #guard_msgs in #eval IO.run do
      let $tm:ident ← TermManager.new
      match ← Solver.run $tm (do $code:term) with
      | .ok res => return res
      | .error e =>
        IO.eprintln ($errPrefStrLit ++ (toString e))
        return default
  )
-- | `(command| test! $tm:ident => $code:term) => `(
--   /-- -/
--   #guard_msgs in #eval IO.run do
--     let $tm:ident ← TermManager.new
--     Solver.runWith! $tm do
--       $code:term
-- )
| `(command|
  $[ $outputComment:docComment ]?
  test! $[ [ $fileId:ident , $testId:ident ] ]? smt $tm:ident => $code:term
) => `(
  $[$outputComment]?
  test! $[ [ $fileId, $testId ] ]? $tm => cvc5.Solver.runWith! $tm $code
)
| `(command|
  $[ $outputComment:docComment ]?
  test! $[ [ $fileId:ident , $testId:ident ] ]? $code:term
) => `(
  $[$outputComment]?
  test! $[ [ $fileId, $testId ] ]? _tm => $code
)
| `(command|
  $[ $outputComment:docComment ]?
  test? $[ [ $fileId:ident, $testId:ident ] ]? $tm:ident => $code:term
) =>
  let errPrefStrLit :=
    match (fileId, testId) with
    | (some fileId, some testId) =>
      Lean.Syntax.mkStrLit s!"[{fileId}.{testId}] test failed:\n"
    | _ => Lean.Syntax.mkStrLit "test failed"
  `(
    #eval IO.run do
      let $tm:ident ← TermManager.new
      match ← Solver.run $tm (do $code:term) with
      | .ok res => return res
      | .error e =>
        IO.eprintln ($errPrefStrLit ++ (toString e))
        return default
  )
-- | `(command| $[ $_outputComment:docComment ]? test? $tm:ident => $code:term) => `(
--   #eval IO.run do
--     let $tm:ident ← TermManager.new
--     Solver.runWith! $tm do
--       $code:term
-- )
| `(command|
  $[ $outputComment:docComment ]?
  test? $[ [ $fileId:ident , $testId:ident ] ]? smt $tm:ident => $code:term
) => `(
  $[$outputComment]?
  test? $[ [ $fileId, $testId ] ]? $tm => cvc5.Solver.runWith! $tm $code
)
| `(command| $[$outputComment]? test? $[ [ $fileId, $testId ] ]? $code:term) => `(
  $[$outputComment]?
  test? $[ [ $fileId, $testId ] ]? _tm => $code
)

end Test

end cvc5
