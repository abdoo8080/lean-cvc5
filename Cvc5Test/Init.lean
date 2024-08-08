import Lean.Server.Utils

import cvc5

namespace cvc5

namespace Test

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

def assertOk [Inhabited α] (code : SolverM α) (hint := "") : SolverM α :=
  fun solver => do
    match ← code solver with
    | (.ok res, solver) => return (.ok res, solver)
    | (.error e, _) =>
      IO.eprintln s!"{Test.pref hint}expected `.ok` result, got {e}"
      fail "assertion failed"

def assertError
  (expected : String) (code : SolverM α) (hint := "")
: SolverM Unit := fun solver => do
  match ← code solver with
  | (.ok _, _) =>
    IO.eprintln s!"{Test.pref hint}expected `.error {expected}`, got `.ok` result"
    fail "assertion failed"
  | (.error err, solver) =>
    let err :=
      match err with
      | .user_error msg => msg
      | .missingValue => "missing value"
    if err = expected then
      return (.ok (), solver)
    else
      IO.eprintln s!"{Test.pref hint}expected `.error {expected}`, got `.error {err}`"
      fail "assertion failed"

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
