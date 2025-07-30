/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Adrien Champion
-/

import Lean.Elab.Command

/-! # Basic types, helpers, and syntax extensions -/
namespace cvc5



/-- Error type. -/
inductive Error where
  | missingValue
  | error (msg : String)
  | recoverable (msg : String)
  | unsupported (msg : String)
  | option (msg : String)
  | parsing (msg : String)
deriving Repr

namespace Error

def toIO : Error → IO.Error
  | .missingValue => IO.Error.userError "missing value"
  | .error msg => IO.Error.userError s!"{msg}"
  | .recoverable msg => IO.Error.userError s!"[recoverable] {msg}"
  | .unsupported msg => IO.Error.userError s!"[unsupported] {msg}"
  | .option msg => IO.Error.userError s!"[option] {msg}"
  | .parsing msg => IO.Error.userError s!"[parsing] {msg}"

/-- String representation of an error. -/
protected def toString : Error → String :=
  toString ∘ repr

/-- Panics on errors, otherwise yields the `ok` result. -/
def unwrap! [Inhabited α] : Except Error α → α
| .ok a => a
| .error e => panic! e.toString

instance : ToString Error :=
  ⟨Error.toString⟩

end Error

section variable [Monad m] [MonadExcept Error m] (msg : String)

def throwMissingValue : m α := throw <| Error.missingValue

protected def throw : m α := throw <| Error.error msg
def throwRecoverable : m α := throw <| Error.recoverable msg
def throwUnsupported : m α := throw <| Error.unsupported msg
def throwOption : m α := throw <| Error.option msg
def throwParsing : m α := throw <| Error.parsing msg

end



/-! ## Syntax extensions for external definitions -/
namespace Ext

open Lean
open Elab
open Command (CommandElab CommandElabM)
open Lean.Parser.Command (visibility)

/-! Aliases for common syntax-related types. -/

abbrev DeclMods := TSyntax ``Lean.Parser.Command.declModifiers
abbrev DeclSig := TSyntax ``Lean.Parser.Command.declSig
abbrev DeclSig? := TSyntax ``Lean.Parser.Command.optDeclSig
abbrev Vis := TSyntax [``Lean.Parser.Command.private, ``Lean.Parser.Command.protected]
abbrev DeclArg := TSyntax ``Lean.Parser.Term.bracketedBinder
abbrev DeclArgs := Array DeclArg

namespace DeclMods
/-- Empty decl-modifiers. -/
def empty : CommandElabM DeclMods := `(declModifiers|)
end DeclMods

/-- Visibility specification: `public` or `private`.

No `protected` because we currently don't need it.
-/
inductive VisSpec
| pub | priv

/-! Helpers over `Lean.Ident`-s. -/
namespace Ident

/-- Absolute version of a `Lean.Ident`. -/
def absolutize (ident : Lean.Ident) : CommandElabM Lean.Ident := do
  let name := ident.getId
  -- This function is a bit tricky because it will be used with `ident` being a protected ident, for
  -- instance on `Term.not` with `ident = 'not'`.
  -- So first, we check if `name` is just a single name bit: if it is, then we just append it to the
  -- current namespace
  if let [bit] := name.components then
    let ns ← getCurrNamespace
    return ns.append bit |> Lean.mkIdentFrom ident.raw
  else match ← resolveGlobalName ident.getId with
    | [ (abs, _) ] => return Lean.mkIdentFrom ident.raw abs
    | [] =>
      Lean.logErrorAt ident.raw s!"failed to resolve identifier `{ident}`"
      throwUnsupportedSyntax
    | (abs, _) :: tail =>
      let msg :=
        s!"ambiguous identifier `{ident}` resolves to {abs}"
        |> tail.foldl fun acc (abs, _) => s!"{acc}, {abs}"
      Lean.logErrorAt ident.raw msg
      throwUnsupportedSyntax

/-- Applies some function to the string version of the last part of an identifier.

Used to generate names for `Option` variants of `Except _ _` function, *i.e.* `get → get?` which is
done directly by function `addQuestionMark`.
-/
def lastBitDo (ident : Lean.Ident) (f : String → String) : Option Lean.Ident :=
  match ident.getId.componentsRev with
  | last :: tail =>
    let last := toString last |> f |> Lean.Name.mkSimple
    -- we have `ident`'s **reverse** components, hence `tail.foldr`
    tail.foldr Lean.Name.append Lean.Name.anonymous
    |>.append last
    |> Lean.mkIdentFrom ident.raw
  | [] => none

/-- Augments the last bit of `ident` with a question mark `?`.

Used to generate names for `Option` variants of `Except _ _` functions.
-/
def addQuestionMark (ident : Lean.Ident) : CommandElabM Lean.Ident := do
  if let some ident := lastBitDo ident (s!"{·}?") then return ident else
    Lean.logErrorAt ident.raw
      s!"cannot retrieve last part of identifier {ident} for `Option` variant generation"
    throwUnsupportedSyntax

end Ident



/-- Result of deconstructing a signature/forall.

Used by env-elaboration to generate the term-manager-taking version and the `Env` version. Also used
where auto-generating the `Option`-variant of an `Except Error _` function.
-/
structure SplitSig where
  /-- Number of explicit arguments in the original signature.

  This is used to auto-generate the body of a variation over the original function `f`, which works
  by constructing a `fun v_1 v_2 ... => <term using f v_1 v_2 ...>` term where the `v_i`-s are the
  explicit arguments of `f`.
  -/
  explicitArgCount : Nat
  /-- All arguments in the original signature. -/
  arguments : DeclArgs
  /-- Return type. -/
  returnType : Lean.Term

namespace SplitSig

/-- Deconstructs the arguments/return type of the input signature. -/
partial def ofDeclSig : DeclSig → CommandElabM SplitSig
  | `(declSig| $[ $lhsArgs ]* : $sig:term) => do
    -- deal with `lhsArgs`
    let mut explArgCount := 0
    let mut args := #[]
    for arg in lhsArgs do
      match arg with
      | `( $bad:hole ) => Lean.logErrorAt bad s!"unexpected hole in external signature"
      | `( $bad:ident ) =>
        Lean.logErrorAt bad s!"unexpected plain identifier with no type in external signature"
      | `(bracketedBinder| $binder:bracketedBinder ) =>
        if let `(bracketedBinder| ($binderArgs* : $_ty $[:= $val]?)) := binder then
          explArgCount := explArgCount + binderArgs.size
        args := args.push binder
    -- now deal with `sig`
    aux explArgCount args sig
  | _ => throwUnsupportedSyntax
where aux (explArgCount : Nat) (args : DeclArgs) : Lean.Term → CommandElabM SplitSig
  -- bracketed binder
  | `(term| $binder:bracketedBinder → $tail) => do
    let explArgCount :=
      if let `(bracketedBinder| ($args* : $_ty $[:= $val]?)) := binder
      then explArgCount + args.size else explArgCount
    aux explArgCount (args.push binder) tail
  -- nameless explicit argument, issues a warning as it's bad for UX
  | `(term| $ty:term → $tail) => do
    let binder ← `(bracketedBinder| (_ : $ty))
    logWarningAt ty "to improve user experience, unnamed arguments are not recommended"
    aux explArgCount.succ (args.push binder) tail
  -- reached the return type
  | `(term| $returnTy:term) => return ⟨explArgCount, args, returnTy⟩

variable (ss : SplitSig)

/-- Generates the `arg1 → arg2 → ... → ty` signature, `arg<i> ∈ ss.arguments`. -/
def addArgs : (ty : Lean.Term) → CommandElabM Lean.Term :=
  -- `foldrM` as we're constructing the signature backwards
  ss.arguments.foldrM fun arg sig => `(term| $arg:bracketedBinder → $sig)

/-- Signature obtained by adding a term manager argument and `Except`-wrapping the return type. -/
def managerTakingTy : CommandElabM Lean.Term := do
  let tmIdent := Lean.mkIdent `cvc5.TermManager
  let exceptIdent := Lean.mkIdent ``Except
  let errorIdent := Lean.mkIdent ``cvc5.Error
  let sigEnd ← `(term| $tmIdent → $exceptIdent $errorIdent $(ss.returnType))
  addArgs ss sigEnd

/-- Signature obtained by `Env ω`-wrapping the return type. -/
def envTy (ω : Ident) : CommandElabM Lean.Term := do
  let envIdent := Lean.mkIdent `cvc5.Env
  let returnTy ← `(term| $envIdent $ω $(ss.returnType))
  let sig ← addArgs ss returnTy
  `( {$ω : Prop} → $sig )

/-- Body of an `Env ω`-function that just calls the term-manager-taking version. -/
def envBody (tmVersionIdent : Lean.Ident) : CommandElabM Lean.Term := do
  let tmVersionIdent ← Ident.absolutize tmVersionIdent
  let mut explicitArgIdents := #[]
  for i in [0:ss.explicitArgCount] do
    explicitArgIdents :=
      explicitArgIdents.push <| Lean.mkIdent <| Lean.Name.mkSimple s!"v_{i.succ}"
  let managerDo? := Lean.mkIdent `cvc5.Env.managerDo?
  `(fun $[ $explicitArgIdents:ident ]* => $managerDo? ($tmVersionIdent $[ $explicitArgIdents ]*))

/-- Unpacks the `α` in `ss.returnType = Except _ α` and updates `ss.returnType` to be `α`.

Used when generating the `Option` variant of an `Except _ _` function.
-/
def unpackExceptReturnType : CommandElabM SplitSig := do
  match ss.returnType with
  | `(term| Except $_errTy:term $ty:term) => return {ss with returnType := ty}
  | `(term| $bad:term) =>
    Lean.logErrorAt bad.raw
      "`ext_def?` requires the return-type of the function to be `Except _ _` \
      to generate an `Option` variant"
    throwUnsupportedSyntax

/-- Type with all arguments and an `Option`-wrapped return type. -/
def optionFunTy : CommandElabM Lean.Term := do
  let optIdent := Lean.mkIdent ``Option
  let returnTy ← `(term| $optIdent $(ss.returnType))
  addArgs ss returnTy

/-- Signature version of `optionFunTy` of the form `: <type>`. -/
def optionFunSig : CommandElabM DeclSig? := do
  let optIdent := Lean.mkIdent ``Option
  let returnTy ← `(term| $optIdent $(ss.returnType))
  let ty ← addArgs ss returnTy
  `(optDeclSig| : $ty)

/-- Body of an `Option`-function that just calls the `Except Error` version. -/
def optionBody (exceptVersionIdent : Lean.Ident) : CommandElabM Lean.Term := do
  let ident ← Ident.absolutize exceptVersionIdent
  let mut explicitArgIdents := #[]
  for i in [0:ss.explicitArgCount] do
    explicitArgIdents :=
      explicitArgIdents.push <| Lean.mkIdent <| Lean.Name.mkSimple s!"v_{i.succ}"
  `(fun $[ $explicitArgIdents:ident ]* =>
    if let .ok res := $ident $[ $explicitArgIdents ]* then some res else none)

end SplitSig



/-- Elaborates an external definition.

- `declMods`: declaration modifiers.
- `defIdent`: identifier of the function being defined.
- `extIdent`: identifier of the external function implementing `defIdent`.
- `defSig`: signature of `defIdent`.
- `forceVis?`: optional visibility specification, overrides `declMods`'s visibility modifier if any.
-/
def externDefElab
  (declMods : DeclMods) (defIdent : Lean.Ident) (extIdent : String) (defSig : DeclSig)
  (forceVis? : Option VisSpec)
: CommandElabM Unit := do
  let extIdent := Lean.Syntax.mkStrLit extIdent defIdent.raw.getHeadInfo
  let declMods ←
    match declMods with
    | `(Parser.Command.declModifiersT|
      $[$doc:docComment]? $[@[ $[ $attrs ],* ]]? $[$vis?]? $[$isNc]? $[$isUnsafe]? $[$opt]?
    ) => do
      let ext ← `(Parser.Term.attrInstance| extern $extIdent:str)
      let attrs := attrs.getD #[] |>.push ext
      let vis? ←
        match forceVis? with
        | none => pure vis?
        | some .pub => pure none
        | some .priv => `(Lean.Parser.Command.private| private)
        -- if let some forceVis := forceVis? then forceVis else vis?
      `(Parser.Command.declModifiersT|
        $[$doc:docComment]? @[ $[$attrs],* ] $[$vis?]? $[$isNc]? $[$isUnsafe]? $[$opt]?
      )
    | _ => throwUnsupportedSyntax
  let stx ← `(
    set_option linter.unusedVariables false in
    $(⟨declMods⟩):declModifiers
    opaque $defIdent $defSig
  )
  Command.elabCommand stx

/-- Elaborates a normal definition.

- `declMods`: declaration modifiers.
- `defIdent`: identifier of the function being defined.
- `defSig?`: optional signature of the declaration.
- `body`: body of the function being defined.
-/
def elabDef
  (declMods : DeclMods) (defIdent : Ident) (defSig? : DeclSig?) (body : Lean.Term)
: CommandElabM Unit := do
  let stx ← `(
    $declMods:declModifiers
    def $defIdent $defSig? := $body:term
  )
  Command.elabCommand stx



/-- Produces the prefix part of an external identifier `<prefix>_<funIdent>`.

At `C++`-level, this prefix roughly corresponds to the name of the type the function is for, with
the first character lowercased: `termManager`, `term`, `sort`, *etc.*

If `forced? = some pref`, then this function just produces `pref`. Otherwise, it retrieves the last
bit of the current namespace's name, turns it into a string, and lowercases the first character.
-/
def extPref : (forced? : Option String) → CommandElabM String
  | none => ofNamespace
  | some pref => return pref
where
  /-- Last bit of the current namespace's name with lowercased first character. -/
  ofNamespace : CommandElabM String := do
    let ns ← getCurrNamespace
    if let super :: _ := ns.componentsRev then
      let ident := super.toString
      return if ident = "Srt" then "sort" else ident.get 0 |>.toLower |> ident.set 0
    else throwError "failed to retrieve current workspace, please provide an explicit extern-prefix"

/-- Produces a complete external identifier `<prefix>_<funIdent>`.

The `<prefix>` part is handled by `extPref`: `extPref pref?`. The `<funIdent>` part is `id` when
`forcedIdent? = some id`, otherwise it's just the string representation of the input `ident`.
-/
def extIdentOf
  (pref? : Option String) (forceIdent? : Option (TSyntax `str)) (ident : Lean.Ident)
: CommandElabM String := do
  let pref ← extPref pref?
  let ident :=
    if let some ident := forceIdent? then ident.getString
    else ident.getId |> toString
  return s!"{pref}_{ident}"



/-- Trace class for debugging the syntax extension. -/
def elabTraceClass := `cvc5.elab
builtin_initialize Lean.registerTraceClass `cvc5.elab

/-- Logs a trace message, use `logTrace!` instead. -/
def logTrace (msg : String) : CommandElabM Unit :=
  Lean.trace elabTraceClass fun () => msg

/-- Logs a trace message. -/
macro "logTrace!" s:interpolatedStr(term) : term => `(cvc5.Ext.logTrace s!$s)

/-- Forces the prefix of extern-identifiers `<prefix>_<funIdent>`.

For instance, `in "termManager"` forces the prefix to `"termManager"`.
-/
declare_syntax_cat cvc5.inPref
@[inherit_doc Lean.Parser.Category.cvc5.inPref]
syntax "in " str : cvc5.inPref

/-- Forces the function identifier of extern-identifier `<prefix>_<funIdent>`. -/
declare_syntax_cat cvc5.asIdent
@[inherit_doc Lean.Parser.Category.cvc5.asIdent]
syntax "as " str : cvc5.asIdent

/-- Syntax for easily specify aliases of an `ext_def`/`env_def`, with visibility modifiers. -/
declare_syntax_cat cvc5.aliases
@[inherit_doc Lean.Parser.Category.cvc5.aliases]
syntax (", " (visibility)? ident)* : cvc5.aliases

/-- Specification of an external definition.

Specifies
- an optional extern-identifier prefix (`inPref`);
- the external definition's identifier;
- an optional extern-identifier function identifier (`asIdent`);
- a list of aliases for the main identifier (`aliases`);
- the signature of the definition.
-/
declare_syntax_cat cvc5.externDefSpec
@[inherit_doc Lean.Parser.Category.cvc5.externDefSpec]
syntax (cvc5.inPref)? ident (cvc5.asIdent)? cvc5.aliases declSig : cvc5.externDefSpec

/-- Additional definitions, optionally follows an `externDefSpec`.

Essentially the same as lean's usual `where` syntax, but uses `with` instead. We don't use `where`
because though the syntax is the same, the semantics is very different from lean's `where` clauses.
Here, `with` specifies standalone definitions after an opaque external definition; lean's `where`
specifies mutually-recursive functions that can call each other.
-/
declare_syntax_cat cvc5.moreDefs
@[inherit_doc Lean.Parser.Category.cvc5.moreDefs]
syntax ppLine withPosition("with " ppLine
  group( colGt declModifiers declId optDeclSig " := " withPosition(group(colGe term)) )+
) : cvc5.moreDefs

/-- An `externDefSpec` followed by an optional `moreDefs`. -/
declare_syntax_cat cvc5.externDefSpecWithDefs
@[inherit_doc Lean.Parser.Category.cvc5.externDefSpecWithDefs]
syntax cvc5.externDefSpec cvc5.moreDefs ? : cvc5.externDefSpecWithDefs

/-- Specifies the identifier to use as the `ω`-scope in `Env` (external or not) definitions. -/
declare_syntax_cat cvc5.omegaScope
@[inherit_doc Lean.Parser.Category.cvc5.omegaScope]
syntax "[" ident "]" : cvc5.omegaScope

/-- Keywords for external definitions.

Keyword `ext_def?` assumes the external definition `myFunction` has a signature with return type
`Except _ α` and generates an `Option α` version called `myFunction?`.
-/
declare_syntax_cat cvc5.extDefKw
@[inherit_doc Lean.Parser.Category.cvc5.extDefKw]
syntax "ext_def " : cvc5.extDefKw
@[inherit_doc Lean.Parser.Category.cvc5.extDefKw]
syntax "ext_def? " : cvc5.extDefKw
/-- Keyword for `Env` external definitions. -/
declare_syntax_cat cvc5.envDefKw
@[inherit_doc Lean.Parser.Category.cvc5.envDefKw]
syntax "env_def " : cvc5.envDefKw
/-- An `extDefKw` or an `envDefKw`, used for definitions inside an `ext_defs` list. -/
declare_syntax_cat cvc5.extDefsKws
@[inherit_doc Lean.Parser.Category.cvc5.extDefsKws]
syntax (cvc5.envDefKw <|> cvc5.extDefKw) : cvc5.extDefsKws

/-- Keyword for a list of external definitions. -/
declare_syntax_cat cvc5.extDefsKw
@[inherit_doc Lean.Parser.Category.cvc5.extDefsKw]
syntax "ext_defs " : cvc5.extDefsKw


syntax (name := externEnvDef)
  declModifiers cvc5.envDefKw (cvc5.omegaScope)? (cvc5.inPref)? cvc5.externDefSpecWithDefs
: command

def externDefElabSpec
  (defaultPref? : Option String) (declMods : DeclMods) (forceVis? : Option VisSpec)
: (stx : TSyntax `cvc5.externDefSpec) → CommandElabM Lean.Ident
  | `(externDefSpec|
    $[in $pref?:str]? $ident:ident $[as $extIdent?:str]?
      $[ , $[$aliasesVis?]? $aliases ]*
      $sig:declSig
  ) => do
    -- syntax `pref?` overrides outer `defaultPref?`
    let pref? := if pref?.isSome then pref?.map TSyntax.getString else defaultPref?
    -- external def
    logTrace! "elab external definition of `{ident}`"
    externDefElab declMods ident (← extIdentOf pref? extIdent? ident) sig forceVis?
    -- aliases
    for (aliasVis?, aliasIdent) in aliasesVis?.zip aliases do
      logTrace! "elab `{ident}` alias `{aliasIdent}`"
      let stx ← `(
        @[inherit_doc $ident]
        $[$aliasVis?]? def $aliasIdent := @$ident
      )
      Command.elabCommand stx
    return ident
  | _ => throwUnsupportedSyntax

def elabEnvExternDefSpec (ω : Lean.Ident) (defaultPref? : Option String) (declMods : DeclMods)
: (stx : TSyntax `cvc5.externDefSpec) → CommandElabM Unit
  | `(externDefSpec|
    $[in $pref?:str]? $ident:ident $[as $extIdent?:str]?
      $[ , $[$aliasesVis?]? $aliases ]*
      $sig:declSig
  ) => do
    let ss ← SplitSig.ofDeclSig sig
    -- syntax `pref?` overrides outer `defaultPref?`
    let pref? := if pref?.isSome then pref?.map TSyntax.getString else defaultPref?

    -- private external def with additional term manager argument and `Except Error`-wrapped return
    -- type
    let withTmIdent := ident.getId |>.append `withManager |> Lean.mkIdent
    logTrace! "elab env-external definition of `{withTmIdent}` for `{ident}`"
    let _ ← do
      let tmSig ← do
        let tmTy ← ss.managerTakingTy
        `(declSig| : $tmTy)
      let envVis := VisSpec.priv
      externDefElab (← DeclMods.empty) withTmIdent (← extIdentOf pref? extIdent? ident) tmSig envVis

    -- env-def and aliases
    let envSig ← do
      let envTy ← ss.envTy ω
      `(optDeclSig| : $envTy)
    let envBody ← ss.envBody withTmIdent

    -- main env-def
    elabDef declMods ident envSig envBody

    -- aliases
    for (aliasVis?, aliasIdent) in aliasesVis?.zip aliases do
      let absIdent ← Ident.absolutize ident
      logTrace! "elab alias {aliasIdent} for {absIdent} ({ident})"
      let stx ← `(
        @[inherit_doc $ident]
        $[$aliasVis?]? def $aliasIdent := @$absIdent
      )
      Command.elabCommand stx
  | _ => throwUnsupportedSyntax

def elabMoreDefs
: (stx : TSyntax `cvc5.moreDefs) → CommandElabM Unit
  | `(moreDefs| with $[ $mods:declModifiers $ident $declSig? := $body]*) => do
    logTrace! "elab more definitions attached to"
    for (mods, ident, sig?, body) in mods.zip <| ident.zip <| declSig?.zip body do
      logTrace! "- `{ident}`"
      let stx ← `($mods:declModifiers def $ident $sig? := $body)
      Command.elabCommand stx
  | _ => throwUnsupportedSyntax

@[command_elab externEnvDef]
unsafe def externEnvDefElab : CommandElab
| `(command|
  $mods:declModifiers
  env_def $[ [ $ω?:ident] ]? $[ in $pref?:str ]?
    $extDefSpec:cvc5.externDefSpec
    $[ $moreDefs?:cvc5.moreDefs ]?
) => do
  let ω ←
    if let some ω := ω? then pure ω else
      Lean.logErrorAt extDefSpec.raw s!"missing `ω`-scope identifier: expected `env_def [ω] ...`"
      throwUnsupportedSyntax
  -- elab env def and aliases
  elabEnvExternDefSpec ω (pref?.map TSyntax.getString) mods extDefSpec
  -- elab more defs if any
  if let some moreDefs := moreDefs? then
    elabMoreDefs moreDefs
| _ => throwUnsupportedSyntax


syntax (name := externExtDef)
  group(declModifiers cvc5.extDefKw (cvc5.inPref)? cvc5.externDefSpecWithDefs)
: command

@[command_elab externExtDef]
unsafe def externExtDefElab : CommandElab
| `(command|
  $mods:declModifiers
  $defKw:cvc5.extDefKw $[ in $pref?:str ]?
    $extDefSpec:cvc5.externDefSpec
    $[ $moreDefs?:cvc5.moreDefs ]?
) => do
  -- elab env def and aliases
  let originalIdent ← externDefElabSpec (pref?.map TSyntax.getString) mods none extDefSpec
  -- generate `Option` variant if asked to
  match defKw with
  | `(extDefKw| ext_def) => pure ()
  | `(extDefKw| ext_def?) => do
    if let `(externDefSpec|
      $[in $_pref?]? $_ident $[as $_extIdent]? $_aliases $sig:declSig
    ) := extDefSpec then
      let ss ← SplitSig.ofDeclSig sig >>= SplitSig.unpackExceptReturnType
      let optDefSig ← ss.optionFunSig
      let optDefBody ← ss.optionBody originalIdent
      let optDefIdent ← Ident.addQuestionMark originalIdent
      elabDef mods optDefIdent optDefSig optDefBody
    else throwUnsupportedSyntax
  | _ => throwUnsupportedSyntax
  -- elab more defs if any
  if let some moreDefs := moreDefs? then
    elabMoreDefs moreDefs
| _ => throwUnsupportedSyntax


syntax (name := externDefs)
  withPosition(cvc5.extDefsKw (cvc5.omegaScope)? (cvc5.inPref)? ppLine group(
    colGt declModifiers cvc5.extDefsKws (cvc5.omegaScope)? (cvc5.inPref)?
      cvc5.externDefSpec (cvc5.moreDefs)?
  )+)
: command

@[command_elab externDefs]
unsafe def externDefsElab : CommandElab
| `(command|
  ext_defs $[ [$topOmega?:ident] ]? $[in $topPref?:str]? $[
    $mods:declModifiers $defKw $[ [$omega?:ident] ]? $[in $pref?:str]?
      $extDefSpec:cvc5.externDefSpec
    $[$moreDefs?:cvc5.moreDefs]?
  ]*
) =>
  for (mods, kw, omega?, pref?, defSpec, moreDefs?) in
    mods.zip <| defKw.zip <| omega?.zip <| pref?.zip <| extDefSpec.zip moreDefs?
  do
    match kw with
    | `(extDefsKws| env_def) =>
      let pref? := if pref?.isSome then pref? else topPref?
      let ω ← match (topOmega?, omega?) with
        | (_, some ω) | (some ω, _) => pure ω
        | (none, none) =>
          Lean.logErrorAt kw.raw
            "no `ω`-scope provided: expected `extern_defs [ω] ...` or `env_def [ω] ...`"
          throwUnsupportedSyntax
      let stx ← `(command|
        $mods:declModifiers
        env_def [$ω] $[in $pref?]? $defSpec:cvc5.externDefSpec $[ $moreDefs?:cvc5.moreDefs ]?
      )
      externEnvDefElab stx
    | `(extDefsKws| ext_def) =>
      let pref? := if pref?.isSome then pref? else topPref?
      if let some ω := omega? then
        Lean.logErrorAt ω.raw "only `env_def`-s specify an `ω`-scope"
        throwUnsupportedSyntax
      let stx ← `(command|
        $mods:declModifiers
        ext_def $[in $pref?]? $defSpec:cvc5.externDefSpec $[ $moreDefs?:cvc5.moreDefs ]?
      )
      externExtDefElab stx
    | _ => throwUnsupportedSyntax
| _ => throwUnsupportedSyntax

end Ext
