/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import cvc5.Term.Manager.Basic



namespace cvc5



section lean_type_to_sort

/-- Specifies that a `cvc5.Sort` corresponding to `α` can be constructed with a `Term.Manager`. -/
class ToCvc5Sort (α : Type u) : Type u where
  /-- Creates a `cvc5.Sort`. -/
  mkCvc5Sort : Term.Manager → cvc5.Sort

opaque ToCvc5Sort.Hack (_ : cvc5.Sort) : Type :=
  Unit

instance : CoeSort cvc5.Sort Type where
  coe sort := ToCvc5Sort.Hack sort

-- @[default_instance]
instance (sort : cvc5.Sort) : ToCvc5Sort (ToCvc5Sort.Hack sort) where
  mkCvc5Sort _ := sort

-- instance instToCvc5SortSort (sort : cvc5.Sort) : ToCvc5Sort sort :=
--   inferInstance

end lean_type_to_sort



namespace Term.Manager



/-! ## Sort creation -/


variable (self : Manager)

open cvc5 (ToCvc5Sort)



@[inherit_doc ToCvc5Sort.mkCvc5Sort]
abbrev mkSort :=
  @ToCvc5Sort.mkCvc5Sort

instance instToCvc5SortBool : ToCvc5Sort Bool :=
  ⟨mkSortBool⟩

instance instToCvc5SortInt : ToCvc5Sort Int :=
  ⟨mkSortInt⟩

-- # TODO
-- `Lean.Rat` is not cvc5's `Real`, maybe a bad idea to have that
instance instToCvc5SortRat : ToCvc5Sort Lean.Rat :=
  ⟨mkSortReal⟩

instance instToCvc5SortString : ToCvc5Sort String :=
  ⟨mkSortString⟩

-- # TODO
-- the resulting sort is indexed by `Int`, might not be a good idea to have this :/
instance instToCvc5SortArray [ToCvc5Sort α] : ToCvc5Sort (Array α) where
  mkCvc5Sort tm :=
    let idxSort := tm.mkSort Int
    let elmSort := tm.mkSort α
    tm.mkSortArray idxSort elmSort

instance instToCvc5BitVec : ToCvc5Sort (BitVec size) where
  mkCvc5Sort tm := tm.mkSortBitVec size



/-! ## Term creation -/

/-- Creates an if-then-else.

- `cnd` must be of sort `Bool`
- `thn` and `els` must have the same sort
-/
def mkIte (cnd thn els : Term) : Term :=
  self.mkTerm .ITE #[cnd, thn, els]

/-- Creates an n-ary equality with `1 < n`.

- all `terms` must have the same sort
-/
def mkEqualN (terms : Array Term) (_ : 1 < terms.size := by simp_arith) : Term :=
  self.mkTerm .EQUAL terms

/-- Creates a binary equality.

- `lft` and `rgt` must have the same sort
-/
def mkEqual (lft rgt : Term) : Term :=
  self.mkEqualN #[lft, rgt]

/-- Creates a negation of the input term.

- `t` must have sort `Bool`
-/
def mkNot (t : Term) : Term :=
  self.mkTerm .NOT #[t]

/-- Creates an implication between two terms.

- `lhs` and `rhs` must have sort `Bool`
-/
def mkImplies (lhs rhs : Term) : Term :=
  self.mkTerm .IMPLIES #[lhs, rhs]
