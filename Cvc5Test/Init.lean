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

def assertNe [ToString α] [BEq α] (lft rgt : α) (hint := "") : IO Unit := do
  if lft == rgt then
    IO.eprintln s!"{Test.pref hint}comparison failed: `{lft}` is the same as `{rgt}`"
    fail "assertion failed"

def assertOk
  (result : Except Error α)
  (hint : String := "")
: IO α := do
  match result with
  | .ok res => return res
  | .error e =>
    IO.eprintln s!"{Test.pref hint}expected `.ok` result, got `{e}`"
    fail "assertion failed"

def assertSolverOk [Inhabited α] (code : SolverM α) (hint := "") : SolverM α :=
  fun solver => do
    let (result, solver) ← code solver
    let _ ← assertOk result hint
    return (result, solver)

def assertError
  (expected : String)
  (errorDo : Error → IO Unit)
  (result : ExceptT Error IO α)
  (hint : String := "")
: IO Unit := do
  match ← result with
  | .ok _ =>
    IO.eprintln s!"{Test.pref hint}expected {expected}, got `.ok` result"
    fail "assertion failed"
  | .error e => errorDo e

def assertCvc5Error
  (expected : String)
  (result : ExceptT Error IO α)
  (hint : String := "")
: IO Unit :=
  assertError s!"cvc5 error `{expected}`"
    (fun
    | .cvc5Error err => do
      if err = expected then
        return ()
      else
        IO.eprintln s!"{Test.pref hint}expected cvc5 error `{expected}`, got cvc5 error `{err}`"
        fail "assertion failed"
    | .userError err => do
        IO.eprintln s!"{Test.pref hint}expected cvc5 error `{expected}`, got user error `{err}`"
        fail "assertion failed"
    | .missingValue => do
        IO.eprintln s!"{Test.pref hint}expected cvc5 error `{expected}`, got missing value error"
        fail "assertion failed"
    )
    result hint

def assertSolverCvc5Error
  (expected : String) (code : SolverM α) (hint := "")
: SolverM Unit := fun solver => do
  let (result, solver) ← code solver
  assertCvc5Error expected result hint
  return (.ok (), solver)

end Test

namespace Solver

variable [Monad m]

def checkSat? : SolverT m (Option Bool) := do
  let res ← Solver.checkSat
  if res.isSat then
    return true
  else if res.isUnsat then
    return false
  else
    return none

def run! [Inhabited α] (query : SolverM α) : IO α := do
  match ← Solver.run (← TermManager.new) query with
  | .ok res => return res
  | .error err => IO.throwServerError err.toString

end Solver

def SolverT.run! [Inhabited α] (query : SolverT IO α) := Solver.run! query

end cvc5
