/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import cvc5.Term.Defs.Basic



namespace cvc5



private opaque Term.ManagerImpl : NonemptyType.{0}

def Term.Manager : Type := Term.ManagerImpl.type



namespace Term.Manager

instance instNonempty : Nonempty Manager := ManagerImpl.property

@[extern "termManager_new"]
opaque mk : BaseIO Manager



/-! ## Sort creation -/


variable (self : Manager)

/-- Boolean sort. -/
@[extern "termManager_mkBooleanSort"]
opaque mkSortBool : Manager → cvc5.Sort

/-- Integer sort. -/
@[extern "termManager_mkIntegerSort"]
opaque mkSortInt : Manager → cvc5.Sort

/-- Real/Rat sort. -/
@[extern "termManager_mkRealSort"]
opaque mkSortReal : Manager → cvc5.Sort

/-- regular expression sort. -/
@[extern "termManager_mkRegExpSort"]
opaque mkSortRegExp : Manager → cvc5.Sort

/-- String sort. -/
@[extern "termManager_mkStringSort"]
opaque mkSortString : Manager → cvc5.Sort

/-- Array sort. -/
@[extern "termManager_mkArraySort"]
opaque mkSortArray : Manager → (idxSort : cvc5.Sort) → (elmSort : cvc5.Sort) → cvc5.Sort

/-- BitVec sort. -/
@[extern "termManager_mkBitVectorSort"]
opaque mkSortBitVec : Manager → (size : Nat) → cvc5.Sort



/-! ## Term creation -/

/-- Creates a boolean constant. -/
@[extern "termManager_mkBoolean"]
opaque mkBoolean : Manager → Bool → Term

@[extern "termManager_mkIntegerFromString"]
private opaque mkIntegerFromString : Manager → String → Term

/-- Creates an integer constant. -/
def mkInteger : Int → Term :=
  self.mkIntegerFromString ∘ toString

/-- Creates an n-ary `Term` of a given `Kind`. -/
@[extern "termManager_mkTerm"]
opaque mkTerm : Manager → Kind → (children : Array Term := #[]) → Term
