/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import cvc5.Init.Basic
import cvc5.Init.Logic
import cvc5.Init.Kind
import cvc5.Init.SortKind



/-! # Type definitions such as `Term`, `Solver`, ...

Most of the types defined here are just plumbing with the C++ cvc5 API.
-/



private opaque cvc5.SortImpl : NonemptyType.{0}

/-- Cvc5 sort.

`Sort` is a keyword in lean, but we can get around this by (always) writing `cvc5.Sort` instead.
-/
def cvc5.Sort : Type := cvc5.SortImpl.type

namespace cvc5.Sort

instance instNonempty : Nonempty cvc5.Sort := SortImpl.property

@[extern "sort_null"]
opaque null : Unit → cvc5.Sort

instance instInhabitedSort : Inhabited cvc5.Sort := ⟨null ()⟩

/-! ## Equality -/

@[extern "sort_beq"]
protected opaque beq : cvc5.Sort → cvc5.Sort → Bool

instance instBEq : BEq cvc5.Sort := ⟨Sort.beq⟩

/-! ## Less than -/

@[extern "sort_blt"]
protected opaque blt : cvc5.Sort → cvc5.Sort → Bool

def lt (s1 s2 : cvc5.Sort) : Prop :=
  s1.blt s2

instance instLT : LT cvc5.Sort := ⟨Sort.lt⟩

instance instDecidableLT (s1 s2 : cvc5.Sort) : Decidable (s1 < s2) :=
  if h : s1.blt s2 then .isTrue h else .isFalse h

/-! ## Less than or equal to -/

@[extern "sort_ble"]
protected opaque ble : cvc5.Sort → cvc5.Sort → Bool

def le (s1 s2 : cvc5.Sort) : Prop :=
  s1.ble s2

instance instLE : LE cvc5.Sort := ⟨Sort.le⟩

instance instDecidableLE (s1 s2 : cvc5.Sort) : Decidable (s1 ≤ s2) :=
  if h : s1.ble s2 then .isTrue h else .isFalse h

/-! ## Hash -/

@[extern "sort_hash"]
protected opaque hash : cvc5.Sort → UInt64

instance : Hashable cvc5.Sort := ⟨Sort.hash⟩

/-! ## Information extraction -/

@[extern "sort_getKind"]
opaque getKind : cvc5.Sort → SortKind

@[extern "sort_getFunctionDomainSorts"]
opaque getFunctionDomainSorts : cvc5.Sort → Array cvc5.Sort

@[extern "sort_getFunctionCodomainSort"]
opaque getFunctionCodomainSort : cvc5.Sort → cvc5.Sort

@[extern "sort_getSymbol"]
opaque getSymbol : cvc5.Sort → String

@[extern "sort_isInteger"]
opaque isInteger : cvc5.Sort → Bool

@[extern "sort_getBitVectorSize"]
opaque getBitVectorSize : cvc5.Sort → UInt32

@[extern "sort_toString"]
protected opaque toString : cvc5.Sort → String

instance instToString : ToString cvc5.Sort := ⟨Sort.toString⟩
instance instRepr : Repr cvc5.Sort := ⟨fun self _ => self.toString⟩

end cvc5.Sort



namespace cvc5



private opaque ResultImpl : NonemptyType.{0}

/-- The result of a `checkSat`-like query: either *sat*, *unsat*, or *unknown*.

Unknown results are typically due to a timeout, or if cvc5 gave up on the check which is not rare in
an undecidable theory.
-/
def Result : Type := ResultImpl.type

instance Result.instNonemptyResult : Nonempty Result := ResultImpl.property

namespace Result

/-- True if this result is from a satisfiable `checkSat`-like query. -/
@[extern "result_isSat"]
opaque isSat : Result → Bool

/-- True if this result is from an unsatisfiable `checkSat`-like query. -/
@[extern "result_isUnsat"]
opaque isUnsat : Result → Bool

/-- True if this result is from a `checkSat`-like query for which cvC5 could not determine
(un)satisfiability.
-/
@[extern "result_isUnknown"]
opaque isUnknown : Result → Bool

/-- String representation. -/
@[extern "result_toString"]
protected opaque toString : Result → String

instance instToString : ToString Result := ⟨Result.toString⟩

end Result



inductive Error where
  | missingValue
  | userError (msg : String)
deriving Repr

instance Error.instToString : ToString Error :=
  ⟨toString ∘ (reprPrec · 1)⟩
