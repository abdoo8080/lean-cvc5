/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import cvc5.Init



namespace cvc5




private opaque OpImpl : NonemptyType.{0}

/-- Cvc5 operator. -/
def Op : Type := OpImpl.type

namespace Op

instance instNonemptyOp : Nonempty Op := OpImpl.property

@[extern "op_null"]
opaque null : Unit → Op

instance instInhabited : Inhabited Op := ⟨null ()⟩

@[extern "op_getKind"]
opaque getKind : Op → Kind

@[extern "op_isNull"]
opaque isNull : Op → Bool

@[extern "op_isIndexed"]
opaque isIndexed : Op → Bool

@[extern "op_getNumIndices"]
opaque getNumIndices : Op → Nat

@[extern "op_toString"]
protected opaque toString : Op → String

instance : ToString Op := ⟨Op.toString⟩

end Op
