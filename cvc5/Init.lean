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
section defsMacro

open Lean
open Elab
open Command (CommandElab CommandElabM)
open Lean.Parser.Command (visibility)

abbrev DeclMods := TSyntax ``Lean.Parser.Command.declModifiers
abbrev DeclSig := TSyntax ``Lean.Parser.Command.declSig
abbrev DeclSig? := TSyntax ``Lean.Parser.Command.optDeclSig
abbrev Vis := TSyntax [``Lean.Parser.Command.private, ``Lean.Parser.Command.protected]
abbrev DeclArg := TSyntax ``Lean.Parser.Term.bracketedBinder
abbrev DeclArgs := Array DeclArg

namespace DeclMods
def empty : CommandElabM DeclMods := `(declModifiers|)
end DeclMods

inductive VisSpec
| pub | priv



/-- Result of deconstructing a signature/forall.

Used by env-elaboration to generate the term-manager-taking version and the `Env` version.
-/
private structure SplitSig where
  /-- Number of explicit arguments in the original signature. -/
  explicitArgCount : Nat
  /-- All arguments in the original signature. -/
  arguments : DeclArgs
  /-- Return type. -/
  returnType : TSyntax `term

namespace SplitSig

/-- Deconstructs the arguments of the input forall term. -/
partial def ofDeclSig : DeclSig → CommandElabM SplitSig
  | `(declSig| $[ $lhsArgs ]* : $sig:term) => do
    let mut explArgCount := 0
    let mut args := #[]
    for arg in lhsArgs do
      match arg with
      | `( $bad:hole ) =>
        Lean.logErrorAt bad s!"unexpected hole in external signature"
      | `( $bad:ident ) =>
        Lean.logErrorAt bad s!"unexpected plain identifier with no type in external signature"
      | `(bracketedBinder| $binder:bracketedBinder ) =>
        if let `(bracketedBinder| ($binderArgs* : $_ty $[:= $val]?)) := binder then
          explArgCount := explArgCount + binderArgs.size
        args := args.push binder
    aux explArgCount args sig
  | _ => throwUnsupportedSyntax
where aux (explArgCount : Nat) (args : DeclArgs) : TSyntax `term → CommandElabM SplitSig
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
def addArgs : (ty : TSyntax `term) → CommandElabM (TSyntax `term) :=
  -- `foldrM` as we're constructing the signature backwards
  ss.arguments.foldrM fun arg sig => `(term| $arg:bracketedBinder → $sig)

/-- Signature obtained by adding a term manager argument and `Except`-wrapping the return type. -/
def managerTakingTy : CommandElabM (TSyntax `term) := do
  let tmIdent := Lean.mkIdent `cvc5.TermManager
  let exceptIdent := Lean.mkIdent ``Except
  let errorIdent := Lean.mkIdent ``cvc5.Error
  let sigEnd ← `(term| $tmIdent → $exceptIdent $errorIdent $(ss.returnType))
  addArgs ss sigEnd

/-- Signature obtained by `Env ω`-wrapping the return type. -/
def envTy (ω : Ident) : CommandElabM (TSyntax `term) := do
  let envIdent := Lean.mkIdent `cvc5.Env
  let returnTy ← `(term| $envIdent $ω $(ss.returnType))
  let sig ← addArgs ss returnTy
  `( {$ω : Prop} → $sig )

/-- Body of an `Env ω`-function that just calls the term-manager-taking version. -/
def envBody (tmVersionIdent : TSyntax `ident) : CommandElabM (TSyntax `term) := do
  let mut explicitArgIdents := #[]
  for i in [0:ss.explicitArgCount] do
    explicitArgIdents :=
      explicitArgIdents.push <| Lean.mkIdent <| Lean.Name.mkSimple s!"v_{i.succ}"
  let managerDo? := Lean.mkIdent `cvc5.Env.managerDo?
  `(fun $[ $explicitArgIdents:ident ]* => $managerDo? ($tmVersionIdent $[ $explicitArgIdents ]*))

/-- Signature obtained by `Option`-wrapping the return type. -/
def optionTy : CommandElabM (TSyntax `term) := do
  let optIdent := Lean.mkIdent ``Option
  let returnTy ← `(term| $optIdent $(ss.returnType))
  addArgs ss returnTy

/-- Body of an `Option`-function that just calls the `Except Error` version. -/
def optionBody (exceptVersionIdent : TSyntax `ident) : CommandElabM (TSyntax `term) := do
  let mut explicitArgIdents := #[]
  for i in [0:ss.explicitArgCount] do
    explicitArgIdents :=
      explicitArgIdents.push <| Lean.mkIdent <| Lean.Name.mkSimple s!"v_{i.succ}"
  `(fun $[ $explicitArgIdents:ident ]* =>
    if let .ok res := $exceptVersionIdent $[ $explicitArgIdents ]* then some res else none)

end SplitSig



def externDefElab
  (declMods : DeclMods) (defIdent : TSyntax `ident) (extIdent : String) (defSig : DeclSig)
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

def elabDef
  (declMods : DeclMods) (defIdent : Ident) (defSig? : DeclSig?) (body : TSyntax `term)
: CommandElabM Unit := do
  let stx ← `(
    $declMods:declModifiers
    def $defIdent $defSig? := $body:term
  )
  Command.elabCommand stx



def extPref : (forced : Option String) → CommandElabM String
  | none => ofNamespace
  | some pref => return pref
where ofNamespace : CommandElabM String := do
  let ns ← getCurrNamespace
  if let super :: _ := ns.componentsRev then
    let ident := super.toString
    return if ident = "Srt" then "sort" else ident.get 0 |>.toLower |> ident.set 0
  else throwError "failed to retrieve current workspace, please provide an explicit extern-prefix"

def extIdentOf
  (pref? : Option String) (forceIdent? : Option (TSyntax `str)) (ident : TSyntax `ident)
: CommandElabM String := do
  let pref ← extPref pref?
  let ident :=
    if let some ident := forceIdent? then ident.getString
    else ident.getId |> toString
  return s!"{pref}_{ident}"

namespace Ext


private def debugElabTraceClass := `cvc5.debugElab
builtin_initialize Lean.registerTraceClass `cvc5.debugElab

private def logTrace (msg : String) : CommandElabM Unit :=
  Lean.trace debugElabTraceClass fun () => msg

macro "logTrace!" s:interpolatedStr(term) : term => `(cvc5.Ext.logTrace s!$s)

declare_syntax_cat inPref
syntax "in " str : inPref

declare_syntax_cat asIdent
syntax "as " str : asIdent

declare_syntax_cat aliases
syntax (", " (visibility)? ident)* : aliases

declare_syntax_cat externDefSpec
syntax (inPref)? ident (asIdent)? aliases declSig : externDefSpec

def externDefElabSpec
  (defaultPref? : Option String) (declMods : DeclMods) (forceVis? : Option VisSpec)
: (stx : TSyntax `externDefSpec) → CommandElabM (TSyntax `ident)
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
: (stx : TSyntax `externDefSpec) → CommandElabM Unit
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
        let tmTy ← SplitSig.managerTakingTy ss
        `(declSig| : $tmTy)
      let envVis := VisSpec.priv
      externDefElab (← DeclMods.empty) withTmIdent (← extIdentOf pref? extIdent? ident) tmSig envVis

    -- env-def and aliases
    let envSig ← do
      let envTy ← SplitSig.envTy ss ω
      `(optDeclSig| : $envTy)
    let envBody ← SplitSig.envBody ss withTmIdent

    -- main env-def
    elabDef declMods ident envSig envBody

    -- aliases
    for (aliasVis?, aliasIdent) in aliasesVis?.zip aliases do
      logTrace! "elab `{ident}` alias `{aliasIdent}`"
      let stx ← `(
        @[inherit_doc $ident]
        $[$aliasVis?]? def $aliasIdent := @$ident
      )
      Command.elabCommand stx
  | _ => throwUnsupportedSyntax

declare_syntax_cat moreDefs
syntax ppLine withPosition("with " ppLine
  group( colGt declModifiers declId optDeclSig " := " withPosition(group(colGe term)) )+
) : moreDefs

def elabMoreDefs
: (stx : TSyntax `moreDefs) → CommandElabM Unit
  | `(moreDefs| with $[ $mods:declModifiers $ident $declSig? := $body]*) => do
    logTrace! "elab more definitions attached to"
    for (mods, ident, sig?, body) in mods.zip <| ident.zip <| declSig?.zip body do
      logTrace! "- `{ident}`"
      let stx ← `($mods:declModifiers def $ident $sig? := $body)
      Command.elabCommand stx
  | _ => throwUnsupportedSyntax

declare_syntax_cat externDefSpecWithDefs
syntax externDefSpec moreDefs ? : externDefSpecWithDefs

declare_syntax_cat omegaScope
syntax "[" ident "]" : omegaScope


declare_syntax_cat envDefKw
syntax "env_def " : envDefKw
declare_syntax_cat extDefKw
syntax "ext_def " : extDefKw
syntax "ext_def? " : extDefKw

declare_syntax_cat extDefsKws
syntax (envDefKw <|> extDefKw) : extDefsKws


syntax (name := externEnvDef)
  group(declModifiers envDefKw (omegaScope)? (inPref)? externDefSpecWithDefs)
: command

@[command_elab externEnvDef]
unsafe def externEnvDefElab : CommandElab
| `(command|
  $mods:declModifiers
  env_def $[ [ $ω?:ident] ]? $[ in $pref?:str ]?
    $extDefSpec:externDefSpec
    $[ $moreDefs?:moreDefs ]?
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
  group(declModifiers extDefKw (inPref)? externDefSpecWithDefs)
: command

@[command_elab externExtDef]
unsafe def externExtDefElab : CommandElab
| `(command|
  $mods:declModifiers
  $defKw:extDefKw $[ in $pref?:str ]?
    $extDefSpec:externDefSpec
    $[ $moreDefs?:moreDefs ]?
) => do
  -- elab env def and aliases
  let originalIdent ← externDefElabSpec (pref?.map TSyntax.getString) mods none extDefSpec
  match defKw with
  | `(extDefKw| ext_def) => pure ()
  | `(extDefKw| ext_def?) => do
    if let `(externDefSpec|
      $[in $_pref?]? $_ident $[as $_extIdent]? $_aliases $sig:declSig
    ) := extDefSpec then
      let ss ← SplitSig.ofDeclSig sig
      match ss.returnType with
      | `(term| Except Error $ty:term) | `(term| Except cvc5.Error $ty:term) =>
        let ss := {ss with returnType := ty}
        let optSig ← do
          let ty ← SplitSig.optionTy ss
          `(optDeclSig| : $ty)
        let optBody ← do
          let ns ← getCurrNamespace
          ns.append originalIdent.getId
          |> Lean.mkIdent
          |> SplitSig.optionBody ss
        let optIdent ← match originalIdent.getId |>.componentsRev with
          | name :: tail =>
            let last := Lean.Name.mkSimple s!"{name}?"
            tail.foldr (init := Lean.Name.anonymous) Lean.Name.append
            |>.append last
            |> Lean.mkIdent
            |> pure
          | _ => do
            Lean.logErrorAt originalIdent.raw
              "cannot retrieve last part of this identifier for `Option`-def elaboration"
            throwUnsupportedSyntax
        elabDef mods optIdent optSig optBody
      | term =>
        Lean.logErrorAt term.raw
          "`ext_def?` requires the return-type of the function to be `Except Error _`"
        throwUnsupportedSyntax
    else throwUnsupportedSyntax
  | _ => throwUnsupportedSyntax
  -- elab more defs if any
  if let some moreDefs := moreDefs? then
    elabMoreDefs moreDefs
| _ => throwUnsupportedSyntax


syntax (name := externDefs)
  withPosition("extern_defs " (omegaScope)? (inPref)? ppLine group(
    colGt declModifiers extDefsKws (omegaScope)? (inPref)? externDefSpec (moreDefs)?
  )+)
: command

@[command_elab externDefs]
unsafe def externDefsElab : CommandElab
| `(command|
  extern_defs $[ [$topOmega?:ident] ]? $[in $topPref?:str]? $[
    $mods:declModifiers $defKw $[ [$omega?:ident] ]? $[in $pref?:str]?
      $extDefSpec:externDefSpec
    $[$moreDefs?:moreDefs]?
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
        env_def [$ω] $[in $pref?]? $defSpec:externDefSpec $[ $moreDefs?:moreDefs ]?
      )
      externEnvDefElab stx
    | `(extDefsKws| ext_def) =>
      let pref? := if pref?.isSome then pref? else topPref?
      if let some ω := omega? then
        Lean.logErrorAt ω.raw "only `env_def`-s specify an `ω`-scope"
        throwUnsupportedSyntax
      let stx ← `(command|
        $mods:declModifiers
        ext_def $[in $pref?]? $defSpec:externDefSpec $[ $moreDefs?:moreDefs ]?
      )
      externExtDefElab stx
    | _ => throwUnsupportedSyntax
| _ => throwUnsupportedSyntax



declare_syntax_cat externDefs

end Ext
