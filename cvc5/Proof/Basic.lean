/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import cvc5.Proof.Defs.RewriteRule
import cvc5.Proof.Defs.Rule

import cvc5.Term.Basic



namespace cvc5



private opaque ProofImpl : NonemptyType.{0}

/-- Cvc5 proof of an *unsat* result. -/
def Proof : Type := ProofImpl.type

instance Proof.instNonemptyProof : Nonempty Proof := ProofImpl.property



namespace Proof

@[extern "proof_null"]
opaque null : Unit → Proof

instance : Inhabited Proof := ⟨null ()⟩

@[extern "proof_getRule"]
opaque getRule : Proof → Rule

@[extern "proof_getRewriteRule"]
opaque getRewriteRule : Proof → RewriteRule

@[extern "proof_getResult"]
opaque getResult : Proof → Term

abbrev toTerm := getResult

@[extern "proof_getChildren"]
opaque getChildren : Proof → Array Proof

@[extern "proof_getArguments"]
opaque getArguments : Proof → Array Term

@[extern "proof_beq"]
protected opaque beq : Proof → Proof → Bool

instance : BEq Proof := ⟨Proof.beq⟩

@[extern "proof_hash"]
protected opaque hash : Proof → UInt64

instance : Hashable Proof := ⟨Proof.hash⟩
