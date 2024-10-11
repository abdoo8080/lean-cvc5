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

declare_syntax_cat externKw

declare_syntax_cat defsItem
declare_syntax_cat defsItemHead
declare_syntax_cat defsItemTail!?
declare_syntax_cat defsItemTail

declare_syntax_cat defsMod

/-- Arity of an expression.

Stolen from [batteries].

[batteries]: https://leanprover-community.github.io/mathlib4_docs/Batteries/Lean/Expr.html#Lean.Expr.forallArity
-/
def forallArity : Expr → Nat
  | .mdata _ b => forallArity b
  | .forallE _ _ body _ => 1 + forallArity body
  | _ => 0

syntax "?" : defsMod
syntax "!" : defsMod
syntax "!?" : defsMod
syntax "?!" : defsMod

scoped syntax (name := defsItemStxHead)
  declModifiers
  ("@[" "force" str "]")?
  "def " defsMod ? ident
: defsItemHead

scoped syntax (name := defsItemStxTail!?)
  withPosition(ppLine "with!? "
    group(
      colGt
      docComment ?
      ident
    )*
  )
: defsItemTail!?

scoped syntax (name := defsItemStxTail)
  withPosition(ppLine "with "
    group(
      colGt
      docComment ?
      declId optDeclSig ":= " withPosition(group(colGe term))
    )*
  )
: defsItemTail

scoped syntax (name := defsItemStx)
  defsItemHead
  declSig
  (defsItemTail!?)?
  (defsItemTail)?
: defsItem

unsafe def elabDefsItem
  (pref : String) (forceMods : Option (TSyntax `defsMod))
: CommandElab
| `(defsItem|
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
    let stx ← `(defsItem|
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
      if let some (.opaqueInfo i) := env.find? fullName then
        pure (forallArity i.type)
      else
        throwError s!"failed to retrieve arity of (opaque) function `{ident}`"

    let mut args := Array.empty
    for i in [0:arity] do
      let arg := Lean.Name.mkSimple s!"v{i}" |> Lean.mkIdent
      args := args.push arg
    let funCall : TSyntax `term ← `(term| ( $fullIdent $[ $args ]* ))

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
| `(defsItem|
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
  let stx ← `(defsItemStx|
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
  withPosition("external! " ("in " str)? ppLine group(colGt defsItem)+)
: command

@[inherit_doc multidefs, command_elab multidefs]
unsafe def multidefsImpl : CommandElab
| `(command|
  external! $[in $pref:str]? $[$defsItems]*
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
        pure super
      else
        throwError "failed to retrieve current workspace, please provide an explicit prefix"
  for defsItem in defsItems do
    elabDefsItem pref none defsItem
| _ => throwUnsupportedSyntax

scoped syntax (name := externkw)
  ("extern_def " <|> "extern_def! " <|> "extern_def? " <|> "extern_def!? " <|> "extern_def?! ")
: externKw

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
    externKw
    ("in " str)?
    ident declSig (defsItemTail)?
  )
: command

@[inherit_doc externdef, command_elab externdef]
unsafe def externdefImpl : CommandElab
| `(command|
  $mods:declModifiers
  $externKw $[in $path:str]? $ident $sig $[$tail]?
) => do
  let defMod ←
    match externKw with
    | `(externKw| extern_def) => pure none
    | `(externKw| extern_def!) => `(defsMod| !)
    | `(externKw| extern_def?) => `(defsMod| ?)
    | `(externKw| extern_def!?) => `(defsMod| !?)
    | `(externKw| extern_def?!) => `(defsMod| ?!)
    | _ => throwUnsupportedSyntax
  let stx ← `(
    external! $[in $path]?
      $mods:declModifiers
      def $[$defMod]? $ident $sig $[$tail:defsItemTail]?
  )
  Command.elabCommand stx
| _ => throwUnsupportedSyntax

end defsMacro
