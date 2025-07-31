import cvc5



/-! # Sanity checks for `Env ω`-scoping -/
namespace Test

open cvc5



/-! # Can't use scoped type values with incompatible term managers -/
namespace Scoping

/-!
The only way we can even try to write something to trigger this problem is to `cvc5.runIO` some
`Env` code when already in `Env` code. However scoped types will not be compatible, which is the
whole point of scoping. (That's assuming functions that should be in `Env` actually are, *i.e.* we
did not make mistakes.)
-/

/--
error: type mismatch
  int'
has type
  Srt ω' : Type
but is expected to have type
  Srt ω : Type
---
error: application type mismatch
  Term.mkConst int
argument
  int
has type
  Srt ω : Type
but is expected to have type
  Srt ω' : Type
---
error: application type mismatch
  List.cons term
argument
  term
has type
  Term ω : Type
but is expected to have type
  Term ω' : Type
-/
#guard_msgs in
def tryToHackIt : Env ω Unit := do
  -- type annotations not needed, added for clarity
  let int : Srt ω ← Srt.Integer
  let term : Term ω ← Term.mkConst int "i"

  -- hacking in progress, `fun {ω'} =>` bit not needed, added for (error) clarity
  cvc5.runIO! fun {ω'} => do
    -- type annotations not needed, added for clarity
    let int' : Srt ω' ← Srt.Integer
    if int = int' then
      --     ^^^^~~~~~ FIRST ERROR HERE
      println! "illegal comparison"
    let badTerm ← Term.mkConst int "i'"
    --   SECOND ERROR HERE ~~~~^^^
    let term' : Term ω' ← Term.mkConst int' "i'"
    let anotherBadTerm ← Term.mk .ADD #[term, term']
    --          THIRD ERROR HERE ~~~~~~~^^^^

/-!
In case it's not obvious, there's no (safety) problem with a *legal* run of `Env` nested in `Env`.
It's probably not a good idea to do it though.

As shown below, one can even perform some (safe) operations over `Term ω` inside an `Env ω'` 🙀
-/

def noSafetyProblemWithThis : Env ω Unit := do
  -- type annotations not needed, added for clarity
  let int : Srt ω ← Srt.Integer
  let i : Term ω ← Term.mkConst int "i"
  let seven : Term ω ← Term.mkInteger 7
  let eleven : Term ω ← Term.mkInteger 11

  let seven_le_i_le_eleven : Term ω ← Term.mk .AND #[
    ← Term.mk .LEQ #[seven, i],
    ← Term.mk .LEQ #[i, eleven],
  ]
  println! "`{seven_le_i_le_eleven}` is a `Term ω`"

  println! "now entering sub-`Env` 🙀"
  -- stealthily running sub-`Env` code, `fun {ω'} =>` not needed, added for clarity
  let isSat ← cvc5.runIO! fun {ω'} => do
    println! "  I'm in"
    -- type annotations not needed, added for clarity
    let int' : Srt ω' ← Srt.Integer
    let term' : Term ω' ← Term.mkConst int' "i'"
    println! "  no problem manipulating my own sub-`Env` types of course: {term'} has sort {int'}"

    println! "  solver stuff..."
    let solver ← Solver.new
    solver.setLogic "ALL"
    solver.setOption "produce-models" "true"
    -- using a `Term ω` while we are in `Env ω'`, but just its `toString` which is perfectly fine
    solver.parseSmtLib s!"\
(declare-fun i () Int)
(assert {seven_le_i_le_eleven})
    "
    let res ← solver.checkSat
    println! "  now exiting sub-`Env`"
    return res.isSat

  let res := if isSat then "sat" else "unsat"
  println! "`{seven_le_i_le_eleven}` is {res} according to sub-`Env`"


/--
info: `(and (<= 7 i) (<= i 11))` is a `Term ω`
now entering sub-`Env` 🙀
  I'm in
  no problem manipulating my own sub-`Env` types of course: |i'| has sort Int
  solver stuff...
  now exiting sub-`Env`
`(and (<= 7 i) (<= i 11))` is sat according to sub-`Env`
-/
#guard_msgs in #eval cvc5.runIO! noSafetyProblemWithThis

end Scoping



/-! # Can't have a value of a scoped type escape its scope -/
namespace NoScopeEscape

def buildSomeTerm : Env ω (Term ω) := do
  Term.mkConst (← Srt.Boolean) "b"

/-- info: Test.NoScopeEscape.buildSomeTerm {ω : Prop} : Env ω (Term ω) -/
#guard_msgs in #check buildSomeTerm

/--
error: type mismatch
  buildSomeTerm
has type
  Env ?m.4006 (Term ?m.4006) : Type
but is expected to have type
  Env ω✝ (Term ?m.4001) : Type
-/
#guard_msgs in #eval do
  let termButManagerIsDead : Term _ ← cvc5.runIO! buildSomeTerm
  println! "bad {termButManagerIsDead}"

end NoScopeEscape




/-! # (Almost) can't use scoped types concurrently -/
namespace WithTasks

/-- info: Task.{u} (α : Type u) : Type u -/
#guard_msgs in #check Task
/-- info:
Task.spawn.{u} {α : Type u} (fn : Unit → α) (prio : Task.Priority := Task.Priority.default) : Task α
-/
#guard_msgs in #check Task.spawn
/-- info: Task.get.{u} {α : Type u} (self : Task α) : α -/
#guard_msgs in #check Task.get

/-!
Using `Task` we actually can run code using, say, `Term ω` concurrently. This code will however not
be able to run `Env ω` code, meaning as long as our API uses `Env ω` where it should this (probably)
not a problem.

It can get tricky because some seemingly non-mutating functions rely on a cache to retrieve their
result, meaning two concurrent calls attempting to retrieve a not-computed-yet result could try to
write the cache at the same time.Note that even creating the value to cache could be a problem, if
it's an `Srt ω` for instance.
-/

/-- Function we're going to run concurrently with itself (on the same `terms`).

Note that this function cannot create terms, sorts, manipulate solvers... as it cannot **run**
`Env ω` code. It can however **create** `Env ω` code concurrently, but this code does literally
nothing unless it is run with `cvc5.run`/`cvc5.runIO`.
-/
def nonEnvFunction (terms : Array (Term ω)) : String := Id.run do
  let mut str := ""
  for term in terms do
    let srt := term.getSort
    str := s!"{str}\n`{term} : {srt}`"
    if let some op := term.getOp? then
      str := s!"{str} has op `{op}`"
    str := term.getChildren.foldl (s!"{·}\n- {·}") str
  return str

/-- Generates some terms. -/
def generateManyTerms (exponent : Nat) : Env ω (Array (Term ω)) := do
  let int ← Srt.Integer
  let zero ← Term.mkInteger 0
  let one ← Term.mkInteger 1
  let i1 ← Term.mkConst int "i1"
  let i2 ← Term.mkConst int "i2"
  let i3 ← Term.mkConst int "i3"
  let i4 ← Term.mkConst int "i4"
  let mut terms := #[zero, one, i1, i2, i3, i4]
  for _ in [0:exponent] do
    terms ← generateTermsFrom terms
  return terms
where generateTermsFrom (base : Array (Term ω)) : Env ω (Array (Term ω)) := do
  let mut res := base
  for term in base do
    for term' in base do
      res := res.push (← term.mkInto .ADD #[term'])
  return res

/-- Uses `Task`, `Task.spawn`, and `Task.get` inside `Env ω`. -/
def concurrent (taskCount : Nat) : Env ω Unit := do
  println! "generating terms..."
  let terms ← generateManyTerms 1
  println! "→ got {terms.size} terms"
  let mut tasks := #[]
  for i in [0:taskCount] do
    println! "spawning task {i.succ}..."
    tasks := tasks.push <| Task.spawn fun () => nonEnvFunction terms
  let mut resString? := none
  println! "waiting for all tasks and validating results"
  for task in tasks do
    let str := task.get.trim
    if let some str' := resString? then
      if str ≠ str' then
        cvc5.throw s!"expected same strings:\n```\n{str'}\n```\n```{str}```"
    else
      resString? := str
  if let some _str := resString? then
    -- println! "result:\n\n```\n{_str.trim}\n```"
    println! "all results have been confirmed to be the same"
  else if taskCount = 0 then
    println! "no tasks were spawned, no result to show"
  else cvc5.throw "fatal, no result string after running all tasks..."

/--
info: generating terms...
→ got 42 terms
spawning task 1...
spawning task 2...
spawning task 3...
spawning task 4...
spawning task 5...
spawning task 6...
spawning task 7...
spawning task 8...
spawning task 9...
spawning task 10...
spawning task 11...
spawning task 12...
spawning task 13...
spawning task 14...
spawning task 15...
spawning task 16...
spawning task 17...
spawning task 18...
spawning task 19...
spawning task 20...
spawning task 21...
spawning task 22...
spawning task 23...
spawning task 24...
waiting for all tasks and validating results
all results have been confirmed to be the same
-/
#guard_msgs in #eval cvc5.runIO! (concurrent 24)

end WithTasks



/-! # Using `IO.asTask` -/
namespace WithIOAsTask

/-- info:
IO.asTask {α : Type} (act : IO α) (prio : Task.Priority := Task.Priority.default) : BaseIO (Task (Except IO.Error α))
-/
#guard_msgs in #check IO.asTask

/-!
`IO.asTask` we can actually run `IO` code concurrently. It's not really a problem since users still
have to call `cvc5.runIO` to turn `Env ω α` into `IO α`, meaning they will use a different term
manager.

Except, `IO` lifts to `Env ω`... so while we're in an `Env ω`, we can

- create (outer) `Term ω` terms;
- spawn a task with `IO.asTask` that runs `Env` code using `cvc5.runIO`, meaning this code uses
  on a **different** term manager than the outer `Env ω`, to create (inner) terms;
- build terms that combine outer and inner sub-terms in that task.

This won't type-check thanks to the scoping mechanism: the `IO` task will use `cvc5.runIO` which
quantifier over its `ω'`, and because of type-checking a `Term ω` cannot be used anywhere in `Env`
functions because it has no reason to be compatible with `ω'`.
-/

export WithTasks (generateManyTerms)

/--
error: application type mismatch
  List.cons term
argument
  term
has type
  Term ω : Type
but is expected to have type
  Term ω' : Type
-/
#guard_msgs in
def tryingToHackIt (taskCount : Nat) : Env ω Unit := do
  let terms ← generateManyTerms 1
  println! "generated {terms.size} terms"

  let mut tasks := #[]
  for i in [0:taskCount] do
    -- `fun {ω'} =>` not needed, added to improve error message's quality
    let task ← IO.asTask (cvc5.runIO! fun {ω'} => do
      let taskInt ← Srt.Integer
      let taskTerm ← Term.mkConst taskInt "j"
      for term in terms do
        let bad ← Term.mk .ADD #[term, taskTerm]
        --       ERROR HERE ~~~~~^^^^
    )
    tasks := tasks.push task

  let mut errors := #[]
  for task in tasks do
    match task.get with
    | .ok () => pure ()
    | .error e =>
      errors := errors.push e
  for error in errors do
    println! "{error}"

end WithIOAsTask



namespace MonadExceptLift

example : MonadExcept String (ExceptT String IO) := inferInstance
example : MonadExceptOf String (EnvT ω (ExceptT String IO)) := inferInstance

def tryCatchString : EnvT ω (ExceptT String IO) String := do
  try throwThe String "stringError"
  catch e : String => return s!"got a string error: {e}"

instance : MonadLift IO (ExceptT String IO) := inferInstance

def runBlah : IO Unit := do
  let res := cvc5.run tryCatchString
  match ← res with
  | .ok (.ok s) => println! "ok ok `{s}`"
  | .ok (.error e) => println! "ok error `{e}`"
  | .error e => println! "ok error `{e}`"

/-- info: ok ok `got a string error: stringError` -/
#guard_msgs in #eval runBlah

end MonadExceptLift
