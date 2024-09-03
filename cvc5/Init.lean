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

declare_syntax_cat defsItem

/-- Arity of an expression.

Stolen from [batteries].

[batteries]: https://leanprover-community.github.io/mathlib4_docs/Batteries/Lean/Expr.html#Lean.Expr.forallArity
-/
def forallArity : Expr → Nat
  | .mdata _ b => forallArity b
  | .forallE _ _ body _ => 1 + forallArity body
  | _ => 0

scoped syntax (name := defsItemStx)
  declModifiers
  ("@[" "force" str "]")?
  "def " ident declSig
  withPosition(ppLine "with "
    group(
      colGt
      docComment ?
      ident
    )*
  )?
  withPosition(ppLine "where "
    group(
      colGt
      docComment ?
      declId optDeclSig ":= " withPosition(group(colGe term))
    )*
  )?
: defsItem

def elabDefsItem (pref : String) : CommandElab
| `(defsItem|
    $mods:declModifiers
    $[ @[ force $forcedName ] ]?
    def $ident:ident $identSig:declSig
    $[ with $[
        $[$autoDoc]?
        $autoId
    ]* ]?
    $[ where $[
        $[$subDoc]?
        $subId $subSig := $subDef
    ]* ]?
) => do
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

  let define doc? id sig? (body : Syntax.Term) : CommandElabM _ := do
    if let some doc := doc? then
      `(command|
        $doc:docComment
        def $id:declId $sig?:optDeclSig := $body
      )
    else
      `(command|
        @[inherit_doc $ident]
        def $id:declId $sig?:optDeclSig := $body
      )

  if let (some autoDoc?, some autoId) := (autoDoc, autoId) then
    let env ← getEnv
    let id := ident.getId.toString
    let name := Lean.Name.mkSimple id
    let ns ← Elab.liftMacroM Macro.getCurrNamespace
    let name := ns.append name
    let arity ←
      if let some (.opaqueInfo i) := env.find? name then
        pure (forallArity i.type)
      else
        throwError s!"failed to retrieve arity of (opaque) function `{ident}`"

    let mut args := Array.empty
    for i in [0:arity] do
      let arg := Lean.Name.mkSimple s!"v{i}" |> Lean.mkIdent
      args := args.push arg
    let funCall : TSyntax `term ← `(term| ($ident $[ $args ]* ))

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
      Command.elabCommand
        (← define autoDoc? autoId (← `(optDeclSig|)) body)

  if let
    (some subDoc?, some subId, some subSig, some subDef)
    := (subDoc, subId, subSig, subDef)
  then
    let all := subDoc?.zip subId |>.zip subSig |>.zip subDef
    for (((subDoc?, subId), subSig), subDef) in all do
      Command.elabCommand
        (← define subDoc? subId subSig subDef)
| _ => throwUnsupportedSyntax

/-- Defines similar functions realized by `extern`.

```
defs "prefix"
  /-- Create a Boolean constant.

  - `b`: The Boolean constant.

  Will create an opaque definition with `[@extern extStr]` where
  `extStr = "prefix" ++ _ ++ "myFunction"`.
  -/
  def myFunction : Term → Except Error Op
  with
    endsWithBang!
    endWithQuestion?
  where
    myOtherFunction : Term → Op :=
      Error.unwrap! ∘ myFunction
    /-- Optional function docstring: if none, inherit from the main function. -/
    yetAnotherFunction : Term → Option Op :=
      Except.toOption ∘ myFunction
```

- `with ...`: takes a sequence of identifiers, each generate a function that
  - unwraps the result if `!`-ended;
  - turns a result into an option if `?`-ended;
  - fails otherwise.

- supports `declModifiers` on the main (`def`) function `myFunction` such as `private`...
- accepts a list of main (`def`) functions, each with `with` and/or `where` clauses.
-/
scoped syntax (name := multidefs)
  withPosition("extern! " str ppLine group(colGt defsItem)+)
: command

@[inherit_doc multidefs, command_elab multidefs]
def multidefsImpl : CommandElab
| `(command|
  extern! $pref:str $[$defsItems]*
) => do
  let pref := pref.getString
  for defsItem in defsItems do
    elabDefsItem pref defsItem
| _ => throwUnsupportedSyntax

end defsMacro
