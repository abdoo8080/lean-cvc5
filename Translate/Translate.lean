import Lean
import Std
import Qq

import cvc5

import Translate.Temp
import Translate.Proof

abbrev XOr (p q : Prop) := ¬(p ↔ q)

open Lean Meta
open Qq
open Smt.Reconstruction

def translateSort (s : cvc5.Sort) : MetaM Expr := do match s.getKind with
  | .BOOLEAN_SORT => return q(Prop)
  | .INTERNAL_SORT_KIND
  | .UNINTERPRETED_SORT => return .fvar ⟨s.toString⟩
  | .BITVECTOR_SORT =>
    let w : Q(Nat) := mkNatLit s.getBitVectorSize.val
    return q(Std.BitVec $w)
  | .INTEGER_SORT => return q(Int)
  | .REAL_SORT => return q(_root_.Rat)
  | _ => return .const `sorry []

partial def translateTerm (t : cvc5.Term) : MetaM Expr := do match t.getKind with
  | .CONSTANT => return .fvar ⟨t.toString⟩
  | .CONST_BOOLEAN => return if t.getBooleanValue then q(True) else q(False)
  | .NOT =>
    let b : Q(Prop) ← translateTerm t[0]!
    return q(¬$b)
  | .IMPLIES =>
    let mut curr : Q(Prop) ← translateTerm t[t.getNumChildren - 1]!
    for i in [1:t.getNumChildren] do
      let p : Q(Prop) ← translateTerm t[t.getNumChildren - i - 1]!
      curr := q($p → $curr)
    return curr
  | .AND => rightAssocOp q(And) t
  | .OR => rightAssocOp q(Or) t
  | .XOR => rightAssocOp q(XOr) t
  | .EQUAL =>
    let α : Q(Type) ← translateSort t[0]!.getSort
    let x : Q($α) ← translateTerm t[0]!
    let y : Q($α) ← translateTerm t[1]!
    return q($x = $y)
  | .DISTINCT =>
    let α : Q(Type) ← translateSort t[0]!.getSort
    let x : Q($α) ← translateTerm t[0]!
    let y : Q($α) ← translateTerm t[1]!
    return q($x ≠ $y)
  | .ITE =>
    mkAppM ``ite #[← translateTerm t[0]!, ← translateTerm t[1]!, ← translateTerm t[2]!]
  | .APPLY_UF =>
    let mut curr ← translateTerm t[0]!
    for i in [1:t.getNumChildren] do
      curr := .app curr (← translateTerm t[i]!)
    return curr
  | .CONST_BITVECTOR =>
    let w : Nat := t.getSort.getBitVectorSize.val
    let v : Nat := (t.getBitVectorValue 10).toNat!
    return q(Std.BitVec.ofNat $w $v)
  | .BITVECTOR_ADD =>
    let w : Nat := t.getSort.getBitVectorSize.val
    let x : Q(Std.BitVec $w) ← translateTerm t[0]!
    let y : Q(Std.BitVec $w) ← translateTerm t[1]!
    return q($x + $y)
  | .ADD =>
    if t.getSort.isInteger then
      let x : Q(Int) ← translateTerm t[0]!
      let y : Q(Int) ← translateTerm t[1]!
      return q($x + $y)
    else
      let x : Q(_root_.Rat) ← translateTerm t[0]!
      let y : Q(_root_.Rat) ← translateTerm t[1]!
      return q($x + $y)
  | .CONST_INTEGER =>
    let x : Int := t.getIntegerValue
    return q($x)
  | _ => return .const `sorry []
where
  rightAssocOp (op : Expr) (t : cvc5.Term) : MetaM Expr := do
    let mut curr ← translateTerm t[t.getNumChildren - 1]!
    for i in [1:t.getNumChildren] do
      curr := mkApp2 op (← translateTerm t[t.getNumChildren - i - 1]!) curr
    return curr

structure TranslateState where
  termMap : HashMap cvc5.Term Name
  proofMap : HashMap cvc5.Proof Name
  steps : Array Step
  trusts : Array cvc5.Proof

-- abbrev TranslateM := StateT TranslateState (cvc5.SolverT MetaM)
abbrev TranslateM := StateT TranslateState MetaM

def getNewName (pre : Name) : TranslateM Name := do
  let state : TranslateState ← get
  return Name.num pre (state.termMap.size + state.proofMap.size)

def addTerm (t : cvc5.Term) (n : Option Name := none) : TranslateM Unit := do
  let state ← get
  if !(state.termMap.contains t) then
    let n := if let some n := n then n else ← getNewName `a
    set { state with termMap := state.termMap.insert t n }

def getTermName (t : cvc5.Term) : TranslateM Name := do
  let state ← get
  return state.termMap.find! t

def addProof (p : cvc5.Proof) (n : Option Name := none) : TranslateM Unit := do
  let n := if let some n := n then n else ← getNewName `s
  let state ← get
  set { state with proofMap := state.proofMap.insert p n }

def isTranslated (p : cvc5.Proof) : TranslateM Bool := do
  let state ← get
  return state.proofMap.contains p

def getProofName (p : cvc5.Proof) : TranslateM Name := do
  let state ← get
  return state.proofMap.find! p

def addStep (s : Step) : TranslateM Unit := do
  let state ← get
  set { state with steps := state.steps.push s }

def addThm (p : Expr) (hp : Expr) : TranslateM Name := do
  let state ← get
  let n ← getNewName `s
  set { state with steps := state.steps.push (.thm n p hp) }
  return n

def addTac (p : Expr) (t : Tac) : TranslateM Name := do
  let state ← get
  let n ← getNewName `s
  set { state with steps := state.steps.push (.tac n p t) }
  return n

def addScope (p : Expr) (as : Array Name) (ss : Array Step) (m : Name) : TranslateM Name := do
  let state ← get
  let n ← getNewName `s
  set { state with steps := state.steps.push (.scope n p as ss m) }
  return n

def addTrust (p : Expr) : TranslateM Name := do
  let state ← get
  let n ← getNewName `s
  set { state with steps := state.steps.push (.trust n p) }
  return n

def addTrustedProof (p : cvc5.Proof) : TranslateM Unit := do
  let state ← get
  set { state with trusts := state.trusts.push p }

def getLastDiff (clause pivot : cvc5.Term) : cvc5.Term := Id.run do
  let mut i := clause.getNumChildren
  while i > 0 do
    if clause[i - 1]! != pivot then
      return clause[i - 1]!
  return cvc5.Term.null ()

def getLastDiffs (clause pivot1 pivot2 : cvc5.Term) : cvc5.Term := Id.run do
  let mut i := clause.getNumChildren
  while i > 0 do
    if clause[i - 1]! != pivot1 && clause[i - 1]! != pivot2 then
      return clause[i - 1]!
  return cvc5.Term.null ()

def getResolutionResult (c₁ c₂ l pol : cvc5.Term) : cvc5.Term := Id.run do
  let l₁ := if pol.getBooleanValue then l else l.not
  let l₂ := if pol.getBooleanValue then l.not else l
  let checkClause (c l : cvc5.Term) (ls : Array cvc5.Term) := Id.run do
    let mut ls := ls
    if c.getKind != .OR then
      if c != l then
        ls := ls.push c
    else
      for li in c do
        if li != l then
          ls := ls.push li
    return ls
  let ls := checkClause c₂ l₂ (checkClause c₁ l₁ #[])
  -- expect `ls` to not be [] (i.e., `false`) in an intermediate chain
  -- resolution step
  if ls.size == 1 then
    return ls[0]!
  let mut curr := ls[0]!
  for i in [1:ls.size] do
    curr := curr.or ls[i]!
  return curr

def getSingletonPosition (clause : cvc5.Term) (pos : Nat) (pivots : Array cvc5.Term) : TranslateM (Option Nat) := do
  if clause.getKind != .OR || (pivots[2 * (pos - 1)]!.getBooleanValue == false && pivots[2 * (pos - 1) + 1]! == clause) then
    return some 0
  if clause[clause.getNumChildren - 1]!.getKind == .OR then
    return clause.getNumChildren
  return none

def translateRewrite (pf : cvc5.Proof) : TranslateM Name := do
  if ← isTranslated pf then
    return ← getProofName pf
  let name ← match pf.getArguments[0]!.getIntegerValue with
  | 48 =>
    let mut args := #[]
    for pfargs in pf.getArguments do
      let mut arg := #[]
      for pfarg in pfargs do
        arg := arg.push (← translateTerm pfarg)
      args := args.push arg
    addTac (← translateTerm pf.getResult) (.rewrite q(Rewrites.Prop.and_assoc_eq) q(and_true) q(Rewrites.Prop.bool_and_true) args)
  | 307 =>
    let α : Q(Type) ← translateSort pf.getArguments[1]!.getSort
    let t : Q($α) ← translateTerm pf.getArguments[1]!
    let s : Q($α) ← translateTerm pf.getArguments[2]!
    addThm q(($t ≠ $s) = ¬($t = $s)) q(@Rewrites.UF.distinct_binary_elim $α $t $s)
  | _ =>
    IO.println pf.getArguments[0]!.getIntegerValue
    let type ← translateTerm pf.getResult
    addTrustedProof pf
    addTrust type
  addProof pf name
  return name

partial def translateStep (pf : cvc5.Proof) : TranslateM Name := do
  if ← isTranslated pf then
    return ← getProofName pf
  let name ← do match pf.getRule with
  | .SCOPE =>
    let state ← get
    set { state with steps := #[] }
    let mut cAssums := #[]
    for arg in pf.getArguments do
      addTerm arg
      cAssums := cAssums.push (← getTermName arg)
    let cMain ← translateStep pf.getChildren[0]!
    let ⟨_, _, cSteps, trusts⟩ ← get
    set { state with trusts := trusts }
    addScope (← translateTerm pf.getResult) cAssums cSteps cMain
  | .ASSUME =>
    getTermName pf.getArguments[0]!
  | .RESOLUTION
  | .CHAIN_RESOLUTION =>
    translateResolution pf
  | .FACTORING =>
    -- as an argument we pass whether the suffix of the factoring clause is a
    -- singleton *repeated* literal. This is marked by a number as in
    -- resolution.
    let children := pf.getChildren
    let lastPremiseLit := children[0]!.getResult[children[0]!.getResult.getNumChildren - 1]!
    let resOriginal := pf.getResult
    -- For the last premise literal to be a singleton repeated literal, either
    -- it is equal to the result (in which case the premise was just n
    -- occurrences of it), or the end of the original clause is different from
    -- the end of the resulting one. In principle we'd need to add the
    -- singleton information only for OR nodes, so we could avoid this test if
    -- the result is not an OR node. However given the presence of
    -- purification boolean variables which can stand for OR nodes (and could
    -- thus be ambiguous in the final step, with the purification remove), we
    -- do the general test.
    let singleton := if lastPremiseLit == resOriginal || (resOriginal.getKind == .OR && lastPremiseLit != resOriginal[resOriginal.getNumChildren - 1]!) then some (children[0]!.getResult.getNumChildren - 1) else none;
    addTac (← translateTerm pf.getResult) (.factor (← translateStep children[0]!) singleton)
  | .REORDERING =>
    let children := pf.getChildren
    let size := pf.getResult.getNumChildren
    let lastPremiseLit := children[0]!.getResult[size - 1]!
    -- none if tail of the clause is not an OR (i.e., it cannot be a singleton)
    let singleton := if lastPremiseLit.getKind == .OR then some (size - 1) else none
    -- for each literal in the resulting clause, get its position in the premise
    let mut pos := #[]
    for resLit in pf.getResult do
      for i in [0:size] do
        if children[0]!.getResult[i]! == resLit then
          pos := pos.push i
    -- turn conclusion into clause
    addTac (← translateTerm pf.getResult) (.reordering (← translateStep children[0]!) pos singleton)
  | .SPLIT =>
    let q : Q(Prop) ← translateTerm pf.getArguments[0]!
    addThm q($q ∨ ¬$q) q(Classical.em $q)
  | .EQ_RESOLVE =>
    let p : Q(Prop) ← translateTerm pf.getChildren[0]!.getResult
    let q : Q(Prop) ← translateTerm pf.getResult
    let hp : Q($p) := .fvar ⟨← translateStep pf.getChildren[0]!⟩
    let hpq : Q($p = $q) := .fvar ⟨← translateStep pf.getChildren[1]!⟩
    addThm q($q) q(Certifying.eqResolve $hp $hpq)
  | .MODUS_PONENS =>
    let p : Q(Prop) ← translateTerm pf.getChildren[0]!.getResult
    let q : Q(Prop) ← translateTerm pf.getResult
    let hp : Q($p) := .fvar ⟨← translateStep pf.getChildren[0]!⟩
    let hpq : Q($p → $q) := .fvar ⟨← translateStep pf.getChildren[1]!⟩
    addThm q($q) q(Certifying.modusPonens $hp $hpq)
  | .NOT_NOT_ELIM =>
    let p : Q(Prop) ← translateTerm pf.getResult
    let hnnp : Q(¬¬$p) := .fvar ⟨← translateStep pf.getChildren[0]!⟩
    addThm q($p) q(Certifying.notNotElim $hnnp)
  | .CONTRA =>
    let p : Q(Prop) ← translateTerm pf.getChildren[0]!.getResult
    let hp : Q($p) := .fvar ⟨← translateStep pf.getChildren[0]!⟩
    let hnp : Q(¬$p) := .fvar ⟨← translateStep pf.getChildren[0]!⟩
    addThm q(False) q(Certifying.contradiction $hp $hnp)
  | .AND_ELIM =>
    addTac (← translateTerm pf.getResult) (.andElim (← translateStep pf.getChildren[0]!) pf.getArguments[0]!.getIntegerValue.toNat)
  | .AND_INTRO =>
    let cpfs := pf.getChildren
    let n := cpfs.size
    let mut q : Q(Prop) ← translateTerm cpfs[n - 1]!.getResult
    let mut hq : Q($q) := .fvar ⟨← translateStep cpfs[n - 1]!⟩
    for i in [1:n] do
      let p : Q(Prop) ← translateTerm cpfs[n - i - 1]!.getResult
      let hp : Q($p) := .fvar ⟨← translateStep cpfs[n - i - 1]!⟩
      hq := .fvar ⟨← addThm q($p ∧ $q) q(And.intro $hp $hq)⟩
      q := q($p ∧ $q)
    return hq.fvarId!.name
  | .NOT_OR_ELIM =>
    addTac (← translateTerm pf.getResult) (.notOrElim (← translateStep pf.getChildren[0]!) pf.getArguments[0]!.getIntegerValue.toNat)
  | .IMPLIES_ELIM =>
    let p : Q(Prop) ← translateTerm pf.getChildren[0]!.getResult[0]!
    let q : Q(Prop) ← translateTerm pf.getChildren[0]!.getResult[1]!
    let hpq : Q($p → $q) := .fvar ⟨← translateStep pf.getChildren[0]!⟩
    addThm q(¬$p ∨ $q) q(Certifying.impliesElim $hpq)
  | .NOT_IMPLIES_ELIM1 =>
    let p : Q(Prop) ← translateTerm pf.getResult
    let q : Q(Prop) ← translateTerm pf.getChildren[0]!.getResult[0]![1]!
    let hnpq : Q(¬($p → $q)) := .fvar ⟨← translateStep pf.getChildren[0]!⟩
    addThm q($p) q(Certifying.notImplies1 $hnpq)
  | .NOT_IMPLIES_ELIM2 =>
    let p : Q(Prop) ← translateTerm pf.getResult
    let q : Q(Prop) ← translateTerm pf.getChildren[0]!.getResult[0]![1]!
    let hnpq : Q(¬($p → $q)) := .fvar ⟨← translateStep pf.getChildren[0]!⟩
    addThm q(¬$q) q(Certifying.notImplies2 $hnpq)
  | .EQUIV_ELIM1 =>
    let p : Q(Prop) ← translateTerm pf.getResult[0]![0]!
    let q : Q(Prop) ← translateTerm pf.getResult[1]!
    let hpq : Q($p = $q) := .fvar ⟨← translateStep pf.getChildren[0]!⟩
    addThm q(¬$p ∨ $q) q(Certifying.equivElim1 $hpq)
  | .EQUIV_ELIM2 =>
    let p : Q(Prop) ← translateTerm pf.getResult[0]!
    let q : Q(Prop) ← translateTerm pf.getResult[1]![0]!
    let hpq : Q($p = $q) := .fvar ⟨← translateStep pf.getChildren[0]!⟩
    addThm q($p ∨ ¬$q) q(Certifying.equivElim2 $hpq)
  | .CNF_AND_POS =>
    let cnf := pf.getArguments[0]!
    let i : Q(Nat) := mkNatLit pf.getArguments[1]!.getIntegerValue.toNat
    let mut ps : Q(List Prop) := q([])
    let n := cnf.getNumChildren
    for i in [0:n] do
      let p : Q(Prop) ← translateTerm cnf[n - i - 1]!
      ps := q($p :: $ps)
    addThm (← translateTerm pf.getResult) q(Certifying.cnfAndPos $ps $i)
  | .CNF_AND_NEG =>
    let cnf := pf.getArguments[0]!
    let mut ps : Q(List Prop) := q([])
    let n := cnf.getNumChildren
    for i in [0:n] do
      let p : Q(Prop) ← translateTerm cnf[n - i - 1]!
      ps := q($p :: $ps)
    addThm (← translateTerm pf.getResult) q(Certifying.cnfAndNeg $ps)
  | .CNF_OR_POS =>
    let cnf := pf.getArguments[0]!
    let mut ps : Q(List Prop) := q([])
    let n := cnf.getNumChildren
    for i in [0:n] do
      let p : Q(Prop) ← translateTerm cnf[n - i - 1]!
      ps := q($p :: $ps)
    addThm (← translateTerm pf.getResult) q(Certifying.cnfOrPos $ps)
  | .CNF_OR_NEG =>
    let cnf := pf.getArguments[0]!
    let i : Q(Nat) := mkNatLit pf.getArguments[1]!.getIntegerValue.toNat
    let mut ps : Q(List Prop) := q([])
    let n := cnf.getNumChildren
    for i in [0:n] do
      let p : Q(Prop) ← translateTerm cnf[n - i - 1]!
      ps := q($p :: $ps)
    addThm (← translateTerm pf.getResult) q(Certifying.cnfOrNeg $ps $i)
  | .REFL =>
    let α : Q(Type) ← translateSort pf.getArguments[0]!.getSort
    let a : Q($α) ← translateTerm pf.getArguments[0]!
    addThm q($a = $a) q(Eq.refl $a)
  | .SYMM =>
    let α : Q(Type) ← translateSort pf.getResult[0]!.getSort
    let a : Q($α) ← translateTerm pf.getResult[1]!
    let b : Q($α) ← translateTerm pf.getResult[0]!
    if pf.getResult.getKind == .EQUAL then
      let h : Q($a = $b) := .fvar ⟨← translateStep pf.getChildren[0]!⟩
      addThm q($b = $a) q(Eq.symm $h)
    else
      let h : Q($a ≠ $b) := .fvar ⟨← translateStep pf.getChildren[0]!⟩
      addThm q($b ≠ $a) q(Ne.symm $h)
  | .TRANS =>
    let cpfs := pf.getChildren
    let mut currName ← translateStep cpfs[0]!
    let a : Q(Type) ← translateTerm cpfs[0]!.getResult[0]!
    for i in [1:cpfs.size] do
      let b : Q(Type) ← translateTerm cpfs[i]!.getResult[0]!
      let c : Q(Type) ← translateTerm cpfs[i]!.getResult[1]!
      let hab : Q($a = $b) := .fvar ⟨currName⟩
      let hbc : Q($b = $c) := .fvar ⟨← translateStep cpfs[i]!⟩
      currName ← addThm q($a = $c) q(Eq.trans $hab $hbc)
    return currName
  | .CONG =>
    let cpfs := pf.getChildren
    let assums ← cpfs.mapM translateStep
    addTac (← translateTerm pf.getResult) (.cong assums)
  | .EVALUATE =>
    addTac (← translateTerm pf.getResult) .eval
  | .DSL_REWRITE =>
    translateRewrite pf
  | .TRUE_INTRO =>
    let p : Q(Prop) ← translateTerm pf.getResult[0]!
    let hp : Q($p) := .fvar ⟨← translateStep pf.getChildren[0]!⟩
    addThm q($p = True) q(Certifying.trueIntro $hp)
  | .TRUE_ELIM =>
    let p : Q(Prop) ← translateTerm pf.getResult[0]!
    let hp : Q($p = True) := .fvar ⟨← translateStep pf.getChildren[0]!⟩
    addThm q($p) q(Certifying.trueElim $hp)
  | .FALSE_INTRO =>
    let p : Q(Prop) ← translateTerm pf.getResult[0]!
    let hnp : Q(¬$p) := .fvar ⟨← translateStep pf.getChildren[0]!⟩
    addThm q($p = False) q(Certifying.falseIntro $hnp)
  | .FALSE_ELIM =>
    let p : Q(Prop) ← translateTerm pf.getResult[0]!
    let hnp : Q($p = False) := .fvar ⟨← translateStep pf.getChildren[0]!⟩
    addThm q(¬$p) q(Certifying.falseElim $hnp)
  | _ =>
    _ ← pf.getChildren.mapM translateStep
    let type ← translateTerm pf.getResult
    addTrustedProof pf
    addTrust type
  addProof pf name
  return name
where
  translateResolution (p : cvc5.Proof) : TranslateM Name := do
    let mut children := p.getChildren.map cvc5.Proof.getResult
    let args := p.getArguments
    let res := p.getResult
    let mut currName ← translateStep p.getChildren[0]!
    let mut curr := children[0]!
    let mut currLastLit := cvc5.Term.null ()
    let mut numCurrLits := 0
    let mut singletons := #[none, none]
    let mut ithPremiseSingleton := Array.ofFn (n := children.size) (fun _ => false)
    -- Whether child 0 is a singleton list. The first child is used as an OR
    -- non-singleton clause if it is not equal to its pivot L_1. Since it's
    -- the first clause in the resolution it can only be equal to the pivot in
    -- the case the polarity is true.
    if children[0]!.getKind != .OR || (args[0]!.getBooleanValue == true && children[0]! == args[1]!) then
      singletons := singletons.set! 0 (some 0)
      currLastLit := children[0]!
      numCurrLits := 1
      ithPremiseSingleton := ithPremiseSingleton.set! 0 true
    else
      ithPremiseSingleton := ithPremiseSingleton.set! 0 false
      numCurrLits := children[0]!.getNumChildren
      currLastLit := children[0]![numCurrLits - 1]!
      if currLastLit.getKind == .OR then
        singletons := singletons.set! 0 (some (numCurrLits - 1))
    -- For all other children C_i the procedure is simliar. There is however a
    -- key difference in the choice of the pivot element which is now the
    -- L_{i-1}, i.e. the pivot of the child with the result of the i-1
    -- resolution steps between the children before it. Therefore, if the
    -- policy id_{i-1} is true, the pivot has to appear negated in the child
    -- in which case it should not be a [(or F1 ... Fn)] node. The same is
    -- true if it isn't the pivot element.
    for i in [1:children.size] do
      singletons := singletons.set! 1 (← getSingletonPosition children[i]! i args)
      ithPremiseSingleton := ithPremiseSingleton.set! i (singletons[1]! == some 0)
      if i < children.size - 1 then
        -- create a (unique) placeholder for the resulting binary
        -- resolution. The placeholder is [res, i, pol, pivot], where pol and
        -- pivot are relative to this part of the chain resolution
        let pol := args[(i - 1) * 2]!
        curr := getResolutionResult curr p.getChildren[i]!.getResult args[(i - 1) * 2 + 1]! pol
        let r := if pol.getBooleanValue then Tac.r0 else Tac.r1
        currName ← addTac (← translateTerm curr) (r currName (← translateStep p.getChildren[i]!) (← translateTerm args[(i - 1) * 2 + 1]!) singletons[0]! singletons[1]!)
        let pivotIndex := 2 * (i - 1)
        -- if the second premise is singleton, the new last current literal
        -- will be:
        -- - if the current last lit is not the pivot, it'll be the new last
        -- - otherwise it'll be the first non-pivot literal in a previous
        -- premise
        if ithPremiseSingleton[i]! then
          -- Note that since this is an internal resolution we cannot have
          -- that both premises are singletons
          -- Assert(numCurrLits > 1);
          -- we only update if currLastLit cannot remain the same
          if currLastLit == (if args[pivotIndex]!.getBooleanValue == true then args[pivotIndex + 1]! else args[pivotIndex + 1]!.not) then
            -- search in a previous premise for the last current literal. For
            -- each j-th previous premise, we look, from last to first, at the
            -- literals that are different from the polarity (j-1)-th pivot
            -- and the !polarity (j-2)-th pivot. We ignore singleton premises
            let mut j := i
            while j > 0 do
              if ithPremiseSingleton[j - 1]! then
                j := j - 1
                continue
              let currPivotIndex := 2 * (j - 1)
              let currPivot := if args[currPivotIndex]!.getBooleanValue == true then args[currPivotIndex]! else args[currPivotIndex]!.not
              let mut diffLit := cvc5.Term.null ()
              -- we also exclude the previous res pivot if there was one,
              -- which is always the case except for the first premise
              if j > 1 then
                let prevPivotIndex := 2 * (j - 2)
                let prevPivot := if args[prevPivotIndex]!.getBooleanValue == true then args[prevPivotIndex]!.not else args[prevPivotIndex]!
                diffLit := getLastDiffs children[j - 1]! currPivot prevPivot
              else
                diffLit := getLastDiff children[j - 1]! currPivot
              if !diffLit.isNull then
                currLastLit := diffLit
                break
              j := j - 1
        else
          currLastLit := getLastDiff children[i]! (if args[pivotIndex]!.getBooleanValue == true then args[pivotIndex + 1]!.not else args[pivotIndex + 1]!)
        -- The number of literals in working clause is what we had before,
        -- plus the literals in the new premise, minus the two literals
        -- removed from it and the new premise.
        numCurrLits :=
            numCurrLits + (if ithPremiseSingleton[i]! then 1 else children[i]!.getNumChildren) - 2;
        -- if the number of current literals is one, then singletons[0] == 0,
        -- otherwise it's != -1 if its last current literal is an OR,
        -- otherwise it's -1
        singletons := singletons.set! 0 (if numCurrLits == 1 then some 0 else (if currLastLit.getKind == .OR then some (numCurrLits - 1) else none))
        -- reset next child to be computed whether singleton
        singletons := singletons.set! 1 none
    let i := children.size - 1
    let r := if args[(i - 1) * 2]!.getBooleanValue then Tac.r0 else Tac.r1
    addTac (← translateTerm res) (r currName (← translateStep p.getChildren.back) (← translateTerm args[(i - 1) * 2 + 1]!) singletons[0]! singletons[1]!)

partial def translateProof (p : cvc5.Proof) : MetaM Proof := do
  -- let .ok (_, ⟨_, _, steps⟩) ← cvc5.Solver.run (StateT.run (translateStep p) ⟨{}, {}, #[]⟩)
    -- | throwError "error translating proof"
  let (_, ⟨_, _, steps, trusts⟩) ← StateT.run (translateStep p) ⟨{}, {}, #[], #[]⟩
  -- let .ok ps ← cvc5.Solver.run (trusts.mapM cvc5.Solver.proofToString)
    -- | throwError "could not print 'trust' steps"
  -- liftM (ps.forM IO.println)
  return steps
