import cvc5



namespace cvc5

def Test.assertEq [Repr α] [BEq α] (lft rgt : α) (hint := "") : IO Unit := do
  if lft != rgt then
    let pref := if hint.isEmpty then "" else s!"[{hint}] "
    IO.eprintln s!"\
{pref}comparison failed: `{reprPrec lft 1}` is different from `{reprPrec rgt 1}\
      "



namespace Solver

variable [Monad m]

def parseAnd (s : String) (andThen : SolverT m α) : SolverT m α := do
  Solver.parse s
  andThen

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

abbrev String.smtParseAnd := @cvc5.Solver.parseAnd
