import Lean.Server.Utils

import cvc5

namespace cvc5

namespace Test

def fail (s : String) : IO Unit :=
  IO.throwServerError s

def assertEq [ToString α] [BEq α] (lft rgt : α) (hint := "") : IO Unit := do
  if lft != rgt then
    let pref := if hint.isEmpty then "" else s!"[{hint}] "
    IO.eprintln s!"{pref}comparison failed: `{lft}` is different from `{rgt}`"
    fail "assertion failed"

def assertNe [ToString α] [BEq α] (lft rgt : α) (hint := "") : IO Unit := do
  if lft == rgt then
    let pref := if hint.isEmpty then "" else s!"[{hint}] "
    IO.eprintln s!"{pref}comparison failed: `{lft}` is the same as `{rgt}`"
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

end Solver

end cvc5
