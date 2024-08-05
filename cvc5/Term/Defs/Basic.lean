/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Lean.Data.Rat

import cvc5.Init
import cvc5.Op.Defs
import cvc5.Term.Defs.SkolemId


namespace cvc5



private opaque TermImpl : NonemptyType.{0}

/-- Cvc5 term. -/
def Term : Type := TermImpl.type

instance Term.instNonemptyTerm : Nonempty Term := TermImpl.property



namespace Term

@[extern "term_null"]
opaque null : Unit → Term

instance : Inhabited Term := ⟨null ()⟩

@[extern "term_isNull"]
opaque isNull : Term → Bool

@[extern "term_getKind"]
opaque getKind : Term → Kind

@[extern "term_getSort"]
opaque getSort : Term → cvc5.Sort

@[extern "term_beq"]
protected opaque beq : Term → Term → Bool

instance : BEq Term := ⟨Term.beq⟩

@[extern "term_hash"]
protected opaque hash : Term → UInt64

instance : Hashable Term := ⟨Term.hash⟩

@[extern "term_getBooleanValue"]
opaque getBooleanValue : Term → Bool

@[extern "term_getBitVectorValue"]
opaque getBitVectorValue : Term → UInt32 → String

@[extern "term_getIntegerValue"]
opaque getIntegerValue : Term → Int

@[extern "term_getRationalValue"]
opaque getRationalValue : Term → Lean.Rat

@[extern "term_hasSymbol"]
opaque hasSymbol : Term → Bool

@[extern "term_getSymbol"]
opaque getSymbol : Term → String

@[extern "term_getId"]
opaque getId : Term → Nat

@[extern "term_getNumChildren"]
opaque getNumChildren : Term → Nat

@[extern "term_isSkolem"]
opaque isSkolem : Term → Bool

@[extern "term_getSkolemId"]
opaque getSkolemId : Term → SkolemId

@[extern "term_getSkolemIndices"]
opaque getSkolemIndices : Term → Array Term

@[extern "term_get"]
protected opaque get : (t : Term) → Fin t.getNumChildren → Term

instance : GetElem Term Nat Term fun t i => i < t.getNumChildren where
  getElem t i h := t.get ⟨i, h⟩

protected def forIn {β : Type u} [Monad m] (t : Term) (b : β) (f : Term → β → m (ForInStep β)) : m β :=
  let rec loop (i : Nat) (h : i ≤ t.getNumChildren) (b : β) : m β := do
    match i, h with
    | 0,   _ => pure b
    | i+1, h =>
      have h' : i < t.getNumChildren := Nat.lt_of_lt_of_le (Nat.lt_succ_self i) h
      have : t.getNumChildren - 1 < t.getNumChildren := Nat.sub_lt (Nat.zero_lt_of_lt h') (by decide)
      have : t.getNumChildren - 1 - i < t.getNumChildren := Nat.lt_of_le_of_lt (Nat.sub_le (t.getNumChildren - 1) i) this
      match (← f t[t.getNumChildren - 1 - i] b) with
      | ForInStep.done b  => pure b
      | ForInStep.yield b => loop i (Nat.le_of_lt h') b
  loop t.getNumChildren (Nat.le_refl _) b

instance : ForIn m Term Term where
  forIn := Term.forIn

def getChildren (t : Term) : Array Term := Id.run do
  let mut cts := #[]
  for ct in t do
    cts := cts.push ct
  cts

@[extern "term_not"]
protected opaque not : Term → Term

@[extern "term_and"]
protected opaque and : Term → Term → Term

@[extern "term_or"]
protected opaque or : Term → Term → Term

@[extern "term_toString"]
protected opaque toString : Term → String

instance : ToString Term := ⟨Term.toString⟩

end Term
