/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Adrien Champion
-/

import Lean.Elab.Command

namespace cvc5

/-! ## DSL for definition  DRY -/
section defsMacro

open Lean
open Elab
open Command (CommandElab CommandElabM)

declare_syntax_cat externKw'

declare_syntax_cat defsItem'
declare_syntax_cat defsItemHead'
declare_syntax_cat defsItemTail!?'
declare_syntax_cat defsItemTail'

declare_syntax_cat defsMod

/-- Arity of an expression.

Stolen from [batteries].

[batteries]: https://leanprover-community.github.io/mathlib4_docs/Batteries/Lean/Expr.html#Lean.Expr.forallArity
-/
def forallArity : Expr → Nat
  | .mdata _ b => forallArity b
  | .forallE _ _ body _ => forallArity body
  | _ => 0

syntax "?" : defsMod
syntax "!" : defsMod
syntax "!?" : defsMod
syntax "?!" : defsMod

scoped syntax (name := defsItemStxHead')
  declModifiers
  ("@[" "force" str "]")?
  "def " defsMod ? ident
: defsItemHead'

scoped syntax (name := defsItemStxTail!?')
  withPosition(ppLine "with!? "
    group(
      colGt
      docComment ?
      ident
    )*
  )
: defsItemTail!?'

scoped syntax (name := defsItemStxTail')
  withPosition(ppLine "with "
    group(
      colGt
      docComment ?
      declId optDeclSig ":= " withPosition(group(colGe term))
    )*
  )
: defsItemTail'

scoped syntax (name := defsItemStx')
  defsItemHead'
  declSig
  (defsItemTail!?')?
  (defsItemTail')?
: defsItem'

unsafe def elabDefsItem
  (pref : String) (forceMods : Option (TSyntax `defsMod))
: CommandElab
| `(defsItem'|
    $mods:declModifiers
    $[ @[ force $forcedName ] ]?
    def $ident:ident $identSig:declSig
    $[ with!? $[
        $[$autoDoc]?
        $autoId
    ]* ]?
    $[ with $[
        $[$subDoc]?
        $subId $subSig := $subDef
    ]* ]?
) => do
  if let some defMods := forceMods then
    let stx ← `(defsItem'|
$mods:declModifiers
$[ @[ force $forcedName ] ]?
def $defMods $ident:ident $identSig:declSig
$[ with!? $[
    $[$autoDoc]?
    $autoId
]* ]?
$[ with $[
    $[$subDoc]?
    $subId $subSig := $subDef
]* ]?
    )
    return ← elabDefsItem pref none stx

  let externName :=
    let id :=
      if let some forcedName := forcedName then
        forcedName.getString
      else
        ident.getId.toString
    pref ++ "_" ++ id |> Syntax.mkStrLit
  -- println! "pref = {pref}"
  let mods ←
    match mods with
    | `(Parser.Command.declModifiersT|
      $[$doc:docComment]? $[@[ $[ $attrs ],* ]]? $[$vis]? $[$isNc]? $[$isUnsafe]? $[$opt]?
    ) => do
      let ext ← `(Parser.Term.attrInstance| extern $externName:str)
      let attrs := attrs.getD #[] |>.push ext
      `(Parser.Command.declModifiersT|
        $[$doc:docComment]? @[ $[$attrs],* ] $[$vis]? $[$isNc]? $[$isUnsafe]? $[$opt]?
      )
    | _ => throwUnsupportedSyntax
  let mainDef ←`(
    set_option linter.unusedVariables false in
    $(⟨mods⟩):declModifiers
    opaque $ident:declId $identSig
  )
  Command.elabCommand mainDef

  let fullName :=
    Lean.Name.mkSimple ident.getId.toString
    |> (← Elab.liftMacroM Macro.getCurrNamespace).append
  let fullIdent := Lean.mkIdent fullName

  let define doc? id sig? (body : Syntax.Term) : CommandElabM _ := do
    if let some doc := doc? then
      `(command|
        $doc:docComment
        def $id:declId $sig?:optDeclSig := $body
      )
    else
      `(command|
        @[inherit_doc $fullIdent]
        def $id:declId $sig?:optDeclSig := $body
      )

  if let (some autoDoc?, some autoId) := (autoDoc, autoId) then
    let env ← getEnv
    let arity ←
      if let some (.opaqueInfo i) := env.find? fullName
      then pure i.type.getForallArity
      else throwError s!"failed to retrieve arity of (opaque) function `{ident}`"

    let mut args := #[ Lean.Name.mkSimple "ω" |> Lean.mkIdent ]
    for i in [0:arity.pred] do
      let arg := Lean.Name.mkSimple s!"v{i}" |> Lean.mkIdent
      args := args.push arg
    let funCall : TSyntax `term ← `(term| ( @ $fullIdent $[ $args ]* ))

    for (autoDoc?, autoId) in autoDoc?.zip autoId do
      let id : String := autoId.getId.toString
      let body ←
        if id.endsWith "!" then
          let unwrapName := Lean.Name.mkStr3 "cvc5" "Error" "unwrap!" |> Lean.mkIdent
          `(fun $[$args]* => $funCall |> $unwrapName)
        else if id.endsWith "?" then
          `(fun $[$args]* => $funCall |> Except.toOption)
        else
          throwError s!"unexpected auto function name `{id}`: expected `<ident>!` or `<ident>?`"
      let cmd ← define autoDoc? autoId (← `(optDeclSig|)) body
      Command.elabCommand cmd

  if let
    (some subDoc?, some subId, some subSig, some subDef)
    := (subDoc, subId, subSig, subDef)
  then
    let all := subDoc?.zip subId |>.zip subSig |>.zip subDef
    for (((subDoc?, subId), subSig), subDef) in all do
      Command.elabCommand
        (← define subDoc? subId subSig subDef)
| `(defsItem'|
    $mods:declModifiers
    $[ @[ force $forcedName ] ]?
    def $defsMod $ident:ident $identSig:declSig
    $[ with $[
        $[$subDoc]?
        $subId $subSig := $subDef
    ]* ]?
) => do
  let name := ident.getId
  let identOpt _ := name.appendAfter "?" |> Lean.mkIdent
  let identPanic _ := name.appendAfter "!" |> Lean.mkIdent
  let auto : Array Ident ←
    match defsMod with
    | `(defsMod| ?) => pure #[identOpt ()]
    | `(defsMod| !) => pure #[identPanic ()]
    | `(defsMod| ?!)
    | `(defsMod| !?) => pure #[identOpt (), identPanic ()]
    | _ => throwUnsupportedSyntax
  let stx ← `(defsItemStx'|
    $mods:declModifiers
    $[ @[ force $forcedName ] ]?
    def $ident:ident $identSig:declSig
    with!? $[ $auto:ident ]*
    $[ with $[
        $[ $subDoc:docComment ]?
        $subId:declId $subSig:optDeclSig := $subDef:term
    ]* ]?
  )
  elabDefsItem pref none stx
| _ => throwUnsupportedSyntax

/-- Defines similar functions realized by `extern`.

```
extern! in "prefix"
  /-- Create a Boolean constant.

  - `b`: The Boolean constant.

  Will create an opaque definition with `[@extern extStr]` where
  `extStr = "prefix" ++ "_" ++ "myFunction"`.
  -/
  def myFunction : Term → Except Error Op
  with!?
    endsWithBang!
    endWithQuestion?
  with
    myOtherFunction : Term → Op :=
      Error.unwrap! ∘ myFunction
    /-- Optional function docstring: if none, inherit from the main function. -/
    yetAnotherFunction : Term → Option Op :=
      Except.toOption ∘ myFunction
```

- `in "prefix"` is optional; if none, then the prefix will be the (last component of the) name of
  the current namespace with the first letter lowercased. Fails if the current namespace has no
  components.

- `with ...`: takes a sequence of identifiers, each generate a function that
  - unwraps the result if `!`-ended, which generates code similar to `myOtherFunction` above;
  - turns a result into an option if `?`-ended, which generates code similar to `yetAnotherFunction`
    above;
  - fails otherwise.

  The `with ...` syntax is currently only compatible with external functions that produce `Except
  Error α` values.

- Supports `declModifiers` on the main (`def`) function `myFunction` such as `private`.
- Accepts a list of external (`def`) functions, each with its `with` clauses.

This macro can generate optional (`?`) and panic (`!`) wrappers even more automatically.

```
extern! "prefix"
  /-- Create a Boolean constant.

  - `b`: The Boolean constant.

  Will create an opaque definition with `[@extern extStr]` where
  `extStr = "prefix" ++ "_" ++ "myFunction"`.
  -/
  def !? myFunction : Term → Except Error Op
  with
    myOtherFunction : Term → Op :=
      myFunction!
    /-- Optional function docstring: if none, inherit from the main function. -/
    yetAnotherFunction : Term → Option Op :=
      myFunction?
```

Notice the `!?` between `def` and `myFunction`. This generates `myFunction!` and `myFunction?` which
respectively panic-unwrap errors and turn the `Except` into an `Option`. In other words, it is the
same as (and internally turned into) a `with!? myFunction! myFunction?` clause using the first
syntax above.

Besides `!?`, the following are also supported:
- `?!`: same behavior as `!?`;
- `!`: only generate the panic unwrapper;
- `?`: only generate the `Option` unwrapper.
-/
scoped syntax (name := multidefs)
  withPosition("external! " ("in " str)? ppLine group(colGt defsItem')+)
: command

@[inherit_doc multidefs, command_elab multidefs]
unsafe def multidefsImpl : CommandElab
| `(command|
  external! $[in $pref:str]? $[$defsItems']*
) => do
  let ns ← getCurrNamespace
  let pref ←
    if let some pref := pref then
      pure pref.getString
    else
      -- println! "componentsRev for {ns.toString}"
      -- for c in ns.componentsRev do
      --   println! "- {c.toString}"
      if let super::_ := ns.componentsRev then
        let mut super := super.toString
        if 0 < super.length then
          super := super.get 0 |>.toLower |> super.set 0
        -- println! "-> `{super}`"
        pure <| if super = "srt" then "sort" else super
      else
        throwError "failed to retrieve current workspace, please provide an explicit prefix"
  for defsItem' in defsItems' do
    elabDefsItem pref none defsItem'
| _ => throwUnsupportedSyntax

scoped syntax (name := externkw)
  ("extern_def " <|> "extern_def! " <|> "extern_def? " <|> "extern_def!? " <|> "extern_def?! ")
: externKw'

/-- Defines an external, opaque function with optional helpers.

```
/-- Some documentation. -/
extern_def!? in "prefix" myFunction : Term → Except Error Op
```

Generates an opaque definition

```
/-- Some documentation. -/
@[extern "prefix_myFunction"]
def myFunction : Term → Except Error Op
```

- `in "prefix"` is optional, uses the current namespace with first letter lowercased if none.

- `extern_def!?` also defines `myFunction! : Term → Op` and `myFunction? : Term → Option Op` in
  terms of `myFunction`.

  Other variants exist:
  - `extern_def?!`: same as `extern_def!?`;
  - `extern_def?`: only defines `myFunction?`;
  - `extern_def!`: only defines `myFunction!`;
  - `extern_def`: defines nothing besides `myFunction`.
-/
scoped syntax (name := externdef)
  declModifiers
  withPosition(
    externKw'
    ("in " str)?
    ident ("as " str)? declSig (defsItemTail')?
  )
: command

@[inherit_doc externdef, command_elab externdef]
unsafe def externdefImpl : CommandElab
| `(command|
  $mods:declModifiers
  $externKw' $[in $path:str]? $ident $[as $altIdent?:str]? $sig $[$tail]?
) => do
  let defMod ←
    match externKw' with
    | `(externKw'| extern_def) => pure none
    | `(externKw'| extern_def!) => `(defsMod| !)
    | `(externKw'| extern_def?) => `(defsMod| ?)
    | `(externKw'| extern_def!?) => `(defsMod| !?)
    | `(externKw'| extern_def?!) => `(defsMod| ?!)
    | _ => throwUnsupportedSyntax
  let stx ← `(
    external! $[in $path]?
      $mods:declModifiers
      $[ @[force $altIdent?] ]?
      def $[$defMod]? $ident $sig $[$tail:defsItemTail']?
  )
  Command.elabCommand stx
| _ => throwUnsupportedSyntax


private def syntaxExtTraceClass := `cvc5.syntaxExt
builtin_initialize Lean.registerTraceClass `cvc5.syntaxExt

def logTrace (msg : String) : CommandElabM Unit := Lean.trace syntaxExtTraceClass fun () => msg



declare_syntax_cat externEnvKw
scoped syntax "extern_env_def " : externEnvKw
scoped syntax "extern_env_def? " : externEnvKw

declare_syntax_cat externEnvDef

/--
Extension for `Env`-monadic definitions that correspond to an external function over a
`TermManager`.

A simple invokation for `mkTerm` would look like this:

```lean
/-- Documentation... -/
extern_env_def? [ω] mkTerm : (kind : Kind) → (children : Array (Term ω)) → Term ω
```

> **NB:** the `[ω]` specifies the identifier for term-manager-scope type parameter used in the
> signature. All types taking a term-manager-scope in the signature should use this identifier:
> `Term ω`, `Srt ω`, *etc.*

This generates two definitions. First, a private opaque one called `mkTerm.withManager` that has the
signature provided in the invokation except

- it has an additional `TermManager` argument as its last argument;
- the original return type is wrapped in `Except Error`, here it would be `Except Error (Term ω)`.

  (Using `extern_env_def` instead of `extern_env_def?` disables this wrapping.)

Assuming the namespace this invokation is in ends with `TermManager`, then `mkTerm.withManager` will
FFI to `termManager_mkTerm`: the first part is the last part of the current namespace with a
lowercased first character, while the second part is the identifier provided in the invokation.
(This can be overridden, see below.)

Hence `mkTerm.withManager`'s definition is:

```lean
@[extern "termManager_mkTerm"]
private opaque mkTerm.withManager
: (kind : Kind) → (children : Array (Term ω)) → TermManager → Except Error (Term ω)
```

> **NB:** this definition is unsafe and thus *always* private. This syntax extension supports
> visibility modifiers but they only apply to the second definition.

The second definition is the `Env`-monadic version of `mkTerm.withManager` which returns an
`Env ω _`, in this example `Env ω (Term ω)`. It relies on `Env.managerDo?` to lift a partial
application of the opaque definition above at `Env`-level.

```lean
/-- Documentation... -/
def mkTerm : (kind : Kind) → (children : Array (Term ω)) → Env ω (Term ω) :=
  fun v0 v1 => Env.managerDo? (mkTerm.withManager v0 v1)
```

> If `extern_env_def` is used instead of `extern_env_def?`, then this definition would use
> `Env.managerDo` instead of `Env.managerDo?`.

## Overriding the C++ function identifier to bind to

The name of the functions we bind at C++ level are built from two parts.

The first one usually corresponds to the type the function is attached to, with a lowercased first
character: `term`, `termManager`, *etc.* This syntax extension retrieves it by using the last part
of the current namespace: if in `cvc5.TermManager` for instance, then `termManager` will be used.

This can be overridden when using this extension with the `in <stringLiteral>` optional syntax:

```lean
namespace Term -- not in `TermManager`

/-- Documentation... -/
extern_env_def? [ω] in "termManager" mkTerm : (kind : Kind) → (children : Array (Term ω)) → Term ω
--                  ^^^^^^^^^^^^^^^^
```

The second part of the name of the C++ functions we bind is the name of the original cvc5 function
itself, *e.g.* `mkTerm`. This syntax extension uses the identifier of the `Env` function being
defined (`mkTerm` in the running example). You can override this with the `as <stringLiteral>`
optional syntax:

```lean
/-- Documentation... -/
extern_env_def? [ω] mk as "mkTerm" : (kind : Kind) → (children : Array (Term ω)) → Term ω
--                     ^^^^^^^^^^^
```

Using both overrides at the same time is fine, for instance one can define `Term.mk` directly with

```lean
namespace Term

/-- Documentation... -/
extern_env_def? [ω] in "termManager" mk as "mkTerm" :
  (kind : Kind) → (children : Array (Term ω)) → Term ω
```

-/
scoped syntax (name := externEnvDefStx)
  declModifiers
  externEnvKw "[" ident "]" ("in " str)? ident ("as " str)? declSig
: command

/-- Generates code for a `TermManager` external definition / `Env` definition pair. -/
unsafe def envCodeGen
  (omegaIdent : Lean.Ident)
  (defMods : TSyntax `Lean.Parser.Command.declModifiers)
  (extDefIdent : Lean.Ident)
  (extFfiNameStr : String)
  (wrapReturnTyInExcept : Bool)
  (envDefIdent : Lean.Ident)
: TSyntax `Lean.Parser.Command.declSig → CommandElabM Unit
-- we don't allow anything on the LHS of the signature's `:`
| `(declSig| $firstArg $_args* : $_ty) => do
  Lean.logErrorAt firstArg "arguments on the left of the signature's `:` are not allowed"
  throwUnsupportedSyntax
-- handle the RHS of the signature's `:`
| `(declSig| : $ty) => deconsForall 0 #[] ty
| _ => throwUnsupportedSyntax
where
  /-- Deconstructs the arguments of the input forall term and calls `codeGen`.

  - `extExplArgCount`: number of explicit argument in the forall; built recursively, default `0`.
  - `extArgs`: array of arguments of the forall; built recursively, default `#[]`.
  -/
  deconsForall (extExplArgCount : Nat) extArgs : TSyntax `term → CommandElabM Unit
    -- bracketed binder
    | `(term| $binder:bracketedBinder → $tail) => do
      let extExplArgCount :=
        if let `(bracketedBinder| ($args* : $_ty $[:= $val]?)) := binder
        then extExplArgCount + args.size else extExplArgCount
      logTrace s!"binder → `{binder}` ({extExplArgCount})"
      deconsForall extExplArgCount (extArgs.push binder) tail
    -- nameless explicit argument, issues a warning as it's bad for UX
    | `(term| $ty:term → $tail) => do
      let binder ← `(bracketedBinder| (_ : $ty))
      logWarningAt ty "to improve user experience, unnamed arguments are not recommended"
      deconsForall extExplArgCount.succ (extArgs.push binder) tail
    -- reached the return type
    | returnTy => do
      logTrace s!"returnTy: {returnTy}"
      codeGen extExplArgCount extArgs returnTy

  /-- Generates the code for the private `TermManager` external function and the `Env` version.

  All arguments are computed by `deconsForall`, which is this function's only caller:

  - `extExplArgCount`: number of explicit argument in the user's forall signature;
  - `extArgs`: all arguments in the user's forall signature;
  - `returnTy`: forall's return type.

  The `TermManager` function's signature will be the same as the user-provided forall signature,
  unless `wrapExtTyInExcept` is true in which case `returnTy` becomes `Except Error <returnTy>`
  (this should be the case for most, if not all, uses of this syntax extension).

  The `Env` version is a just a call to `f` through `Env.managerDo`/`Env.managerDo?`
  decided by the value of `wrapReturnTyInExcept`, *resp.* false/true.
  -/
  codeGen (extExplArgCount : Nat) extArgs returnTy : CommandElabM Unit := do
    -- build all the identifiers we need
    let envTypeIdent := Lean.mkIdent `cvc5.Env
    let managerTypeIdent := Lean.mkIdent `cvc5.TermManager
    let managerLiftFunIdent := Lean.mkIdent <|
      if wrapReturnTyInExcept then `cvc5.Env.managerDo? else `cvc5.Env.managerDo

    -- return type of the `TermManager` (external) function
    let extDefReturnTy : term ←
      if wrapReturnTyInExcept then
        -- asked to wrap the result type with `Except Error`
        let exceptTypeIdent := Lean.mkIdent ``Except
        let errorTypeIdent := Lean.mkIdent `cvc5.Error
        `(term| $exceptTypeIdent $errorTypeIdent $returnTy)
      else
        -- no `Except Error` wrap asked, leave as provided by users
        pure returnTy

    -- ## signatures of the functions we generate code for, built below
    -- `TermManager` external signature, ends with `TermManager → $extDefReturnTy`. The reason we
    -- want the `TermManager` argument to be the last one is that the `Env` definition can build a
    -- `TermManager → Except Error _` function by passing all the explicit arguments to the
    -- `TermManager` function. Then it can just pass that to `Env.managerDo?` as it expects a
    -- `TermManager → Except Error _`.
    let mut extDefSig ← `(term| $managerTypeIdent → $extDefReturnTy)
    -- `Env` signature, ends with `Env ω $returnTy`
    let mut envDefSig ← `(term| $envTypeIdent $omegaIdent $returnTy)

    -- go through all arguments **in reverse** and left-extend `TermManager` and `Env` signatures
    for extArg in extArgs.reverse do
      extDefSig ← `(term| $extArg:bracketedBinder → $extDefSig:term)
      envDefSig ← `(term| $extArg:bracketedBinder → $envDefSig:term)
    logTrace s!"extDefSig = `{extDefSig}`"
    logTrace s!"envDefSig = `{envDefSig}`"

    -- time to elaborate the external `TermManager` function (named `extDefIdent`)
    let _extCodeGen ← do
      -- `@[extern $extFfiNameStr]` attribute
      let externAttr ← do
        let extStr := Lean.Syntax.mkStrLit extFfiNameStr
        `(Parser.Term.attrInstance| extern $extStr:str)
      -- put everything together and elaborate
      let extDef ← `(command|
        @[$externAttr] private opaque $extDefIdent : $extDefSig
      )
      logTrace s!"extDef = {extDef}"
      Command.elabCommand extDef

    /-
    moving on to the `Env` version; the body of this function will be

    `fun v_0 v_1 ... => Env.managerDo? ($extDefIdent v_0 v_1 ...)`

    where each `v_i` stands for the `i`th explicit parameter of the `TermManager` function. Thus,
    there are `extExplArgCount` of them.
    -/

    -- build the `Env` definition's body
    let envDefBody ← do
      -- generate the right number of `v_i` identifiers
      let envDefArgs ← do
        let mut envDefArgs := #[]
        for explArgIdx in [0:extExplArgCount] do
          let explArgIdent := Lean.mkIdent <| Lean.Name.mkSimple s!"v{explArgIdx}"
          let explArgTerm ← `(term| $explArgIdent)
          envDefArgs := envDefArgs.push explArgTerm
        pure envDefArgs
      logTrace s!"envDefArgs = {envDefArgs}"
      -- generate the body
      `(term| fun $envDefArgs* => $managerLiftFunIdent ($extDefIdent $envDefArgs*))
    logTrace s!"envDefBody = {envDefBody}"

    -- Last, put everything together and elaborate. The way we build the syntax is a bit special,
    -- this is to make it as difficult as possible to mess up the term-manager-scope type parameter
    -- (usually called `ω`).
    --
    -- Signatures should only ever use **one**, which is user-provided in the top-level syntax
    -- extension invokation (see `externEnvDefElab`: it's the `ω` in `extern_env_def [ω] ...`).
    --
    -- First we `set_option autoImplicit false`: this catches mistakes like `Term w` (`≠ Term ω`)
    -- and more generally any use of a term-manager-scope type different from the one provided in
    -- the top-level syntax extension. It's not perfect: users can still add `{w : Type}`, but
    -- catching that would require a much deeper dive into the users' signatures.
    --
    -- Second we add an `{$omegaIdent : Type}` argument explicitely. Otherwise we would get an error
    -- due to the `set_option autoImplicit false` above.
    let envDefStx ← do
      `(command|
        set_option autoImplicit false in
        $defMods:declModifiers
        def $envDefIdent {$omegaIdent : Type} : $envDefSig := $envDefBody
      )
    logTrace s!"envDef = {envDefStx}"
    Command.elabCommand envDefStx


@[command_elab externEnvDefStx, inherit_doc externEnvDefStx]
unsafe def externEnvDefElab : CommandElab
| `(command| $mods:declModifiers
  $kw:externEnvKw [ $omega:ident ] $[in $path?:str]? $ident:ident $[as $altIdent?:str]? $sig:declSig
) => do
  -- asked to wrap the `TermManager` external definition's return type in `Except Error`?
  let wrapReturnTyInExcept ←
    match kw with
    | `(externEnvKw| extern_env_def) => pure false
    | `(externEnvKw| extern_env_def?) => pure true
    | _ =>
      logErrorAt kw "unexpected keyword: expected `extern_env_def` or `extern_env_def?`"
      throwUnsupportedSyntax
  -- build the string that must be given to the `extern` attribute for FFI to work; this string has
  -- form `{extPath}_{extIdent}`, *e.g.* `termManager_mkTerm`
  let extStr ← do
    -- the prefix of `extStr`, *e.g.* `"termManager"`
    let extPath ← do
      -- just the user-provided path if any
      if let some path := path? then pure path.getString
      else
        -- otherwise take the last part of the current namespace's `Lean.Name` and lowercase the
        -- first character
        let ns ← getCurrNamespace
        if let super::_ := ns.componentsRev then
          let super := super.toString.modify 0 Char.toLower
          pure <| if super = "srt" then "sort" else super
        else
          throwError "failed to retrieve current workspace, please provide an explicit prefix"
    let extIdent :=
      if let some altIdent := altIdent? then altIdent.getString else s!"{ident.getId}"
    pure <| extPath ++ "_" ++ extIdent
  logTrace s!"extStr = `{extStr}`"
  -- identifier of the private, external definition that takes a `TermManager`
  let extIdent := mkIdent <| (ident.getId : Name).append (Name.mkSimple "withManager")
  logTrace s!"extIdent = `{extIdent}`"
  -- pass everything to codegen
  envCodeGen
    (mkIdent omega.getId) mods extIdent extStr wrapReturnTyInExcept (mkIdent ident.getId) sig
| _ => throwUnsupportedSyntax


declare_syntax_cat manyEnvDefsKw
scoped syntax "extern_env_defs " : manyEnvDefsKw

declare_syntax_cat manyEnvDefsDefKw
scoped syntax "def " : manyEnvDefsDefKw
scoped syntax "def? " : manyEnvDefsDefKw

scoped syntax (name := manyEnvDefsStx)
  withPosition(manyEnvDefsKw "[" ident "]" ("in " str)? ppLine group(
    colGt declModifiers manyEnvDefsDefKw ident ("as " str)? declSig
  )+)
: command

@[command_elab manyEnvDefsStx, inherit_doc externEnvDefStx]
unsafe def manyEnvDefsElab : CommandElab
| `(command|
  extern_env_defs [ $omega:ident ] $[in $path?:str]?
    $[ $mods:declModifiers $defKw $ident:ident $[as $altIdent?:str]? $sig:declSig ]*
) => do
  let many := mods.zip <| defKw.zip <| ident.zip <| altIdent?.zip sig
  for (mods, kw, ident, altIdent?, sig) in many do
    let thisKw ← match kw with
      | `(manyEnvDefsDefKw| def) => `(externEnvKw| extern_env_def)
      | `(manyEnvDefsDefKw| def?) => `(externEnvKw| extern_env_def?)
      | _ => throwUnsupportedSyntax
    let stx ← `(
      $mods:declModifiers
      $thisKw:externEnvKw [$omega:ident] $[in $path?]? $ident:ident $[as $altIdent?]? $sig:declSig
    )
    Command.elabCommand stx
| _ => throwUnsupportedSyntax

end defsMacro
