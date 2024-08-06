import cvc5

namespace cvc5

def Test.assertEq [ToString α] [BEq α] (lft rgt : α) (hint := "") : IO Unit := do
  if lft != rgt then
    let pref := if hint.isEmpty then "" else s!"[{hint}] "
    IO.eprintln s!"{pref}comparison failed: `{lft}` is different from `{rgt}`"

def Test.assertNe [ToString α] [BEq α] (lft rgt : α) (hint := "") : IO Unit := do
  if lft == rgt then
    let pref := if hint.isEmpty then "" else s!"[{hint}] "
    IO.eprintln s!"{pref}comparison failed: `{lft}` is the same as `{rgt}`"

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

def run! [Inhabited α] (tm : TermManager) (query : SolverT m α) : m α := do
  match ← Solver.run tm query with
  | .ok res => return res
  | .error err => panic! s!"solver query failed: {err}"

end Solver

end cvc5
