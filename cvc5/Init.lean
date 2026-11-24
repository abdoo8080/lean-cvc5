/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Adrien Champion
-/

module

public meta import Lean.Elab.Command

namespace cvc5.Init

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
meta def forallArity : Expr → Nat
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

/-! ### Argument ownership

The C++ functions behind `extern_def` only read their object arguments, so `extern_def` declares
every explicit argument borrowed (`@&`): the caller keeps its reference, and the C++ side must not
release it. (Owned, Lean would expect the C++ side to release it, and every argument would leak.)

An argument the C++ side consumes (releases, or returns as its result) is marked `owned t` instead.

Lean drops a borrow annotation on an argument with a default value (`(x : @& t := d)` is owned),
and `@& optParam t d` loses the default. So the external function of a signature with default
values is a separate `opaque` `name.ffi` without them, and `name` is an inline wrapper with them.
-/

/-- Marks an argument of an `extern_def` owned: the C++ function consumes it. Elsewhere, `owned t`
is `t`. -/
scoped syntax:max (name := ownedArg) "owned " term:max : term

@[macro ownedArg]
public meta def expandOwnedArg : Macro
| `(owned $t) => pure t
| _ => Macro.throwUnsupported

/-- The type of an external function's argument: `t` itself if marked `owned` (or already `@&`),
`@& t` otherwise. -/
meta def borrowArgType (t : Term) : CommandElabM Term :=
  match t with
  | `(owned $t) => pure t
  | `(@& $_) => pure t
  | _ => `(@& ($t))

/-- Declares borrowed the explicit arguments of the type of an external function (see
`borrowArgType`), and drops their default values. The state records whether any was dropped. -/
meta partial def borrowType (t : Term) : StateT Bool CommandElabM Term := do
  match t with
  | `($a → $b) => `($(← borrowArgType a) → $(← borrowType b))
  | `(($xs* : $a) → $b) => `(($xs* : $(← borrowArgType a)) → $(← borrowType b))
  | `(($xs* : $a := $_) → $b) =>
    set true
    `(($xs* : $(← borrowArgType a)) → $(← borrowType b))
  | _ => pure t

/-- `borrowType`, on the binders before the colon of a signature. Also returns the names they
bind. -/
meta def borrowBinder (b : Syntax) : StateT Bool CommandElabM (Syntax × Array Ident) := do
  let names (xs : Array Syntax) : StateT Bool CommandElabM (Array Ident) :=
    xs.mapM fun x =>
      if x.isIdent then pure ⟨x⟩ else throwErrorAt x "`extern_def`: name this argument"
  match b with
  | `(bracketedBinder| ($xs* : $a)) =>
    return (← `(bracketedBinder| ($xs* : $(← borrowArgType a))), ← names xs)
  | `(bracketedBinder| ($xs* : $a := $_)) =>
    set true
    return (← `(bracketedBinder| ($xs* : $(← borrowArgType a))), ← names xs)
  | `(bracketedBinder| ($xs* := $d)) =>
    set true
    return (← `(bracketedBinder| ($xs* : @& (type_of% $d))), ← names xs)
  | _ => throwErrorAt b "`extern_def`: unsupported binder"

/-- Adds attribute `attr` to the modifiers `mods`. -/
meta def addAttr (mods : TSyntax ``Parser.Command.declModifiers) (attr : TSyntax ``Parser.Term.attrInstance) :
    CommandElabM (TSyntax ``Parser.Command.declModifiers) := do
  match mods with
  | `(Parser.Command.declModifiersT|
    $[$doc:docComment]? $[@[ $[ $attrs ],* ]]? $[$vis]? $[$isNc]? $[$isUnsafe]? $[$opt]?
  ) => do
    let attrs := attrs.getD #[] |>.push attr
    let mods ← `(Parser.Command.declModifiersT|
      $[$doc:docComment]? @[ $[$attrs],* ] $[$vis]? $[$isNc]? $[$isUnsafe]? $[$opt]?
    )
    return ⟨mods⟩
  | _ => throwUnsupportedSyntax

meta unsafe def elabDefsItem
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
  -- println! "extern name := `{externName}`"
  let ext ← `(Parser.Term.attrInstance| extern $externName:str)
  let (binders, type) : Array Syntax × Term ←
    match identSig with
    | `(Parser.Command.declSig| $bs* : $type) => pure (TSyntaxArray.raw bs, type)
    | _ => throwUnsupportedSyntax
  let ((ffiBinders, argNames, ffiType), hasDefaults) ← (do
      let bs ← binders.mapM borrowBinder
      return (bs.map Prod.fst, bs.flatMap Prod.snd, ← borrowType type)
    ).run false
  let ffiSig : TSyntax ``Parser.Command.declSig :=
    ⟨mkNode ``Parser.Command.declSig
      #[mkNullNode ffiBinders, ← `(Parser.Term.typeSpec| : $ffiType)]⟩
  if hasDefaults then
    -- See "Argument ownership" above.
    let ffiIdent := Lean.mkIdent (ident.getId ++ `ffi)
    Command.elabCommand (← `(
      set_option linter.unusedVariables false in
      /-- The external function of the wrapper without `.ffi`, with no default values. -/
      @[$ext:attrInstance]
      opaque $ffiIdent:declId $ffiSig
    ))
    let mods ← addAttr mods (← `(Parser.Term.attrInstance| inline))
    let wrapperSig : TSyntax ``Parser.Command.optDeclSig :=
      ⟨mkNode ``Parser.Command.optDeclSig #[identSig.raw[0], mkNullNode #[identSig.raw[1]]]⟩
    Command.elabCommand (← `(
      $mods:declModifiers
      def $ident:declId $wrapperSig:optDeclSig := $ffiIdent $argNames*
    ))
  else
    Command.elabCommand (← `(
      set_option linter.unusedVariables false in
      $(← addAttr mods ext):declModifiers
      opaque $ident:declId $ffiSig
    ))

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
      if let some i := env.find? fullName then
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
public meta unsafe def multidefsImpl : CommandElab
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
          super := String.Pos.Raw.get super 0 |>.toLower |> String.Pos.Raw.set super 0
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
public meta unsafe def externdefImpl : CommandElab
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

end cvc5.Init
