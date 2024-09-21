/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import cvc5.Autogen

namespace cvc5


cppEnumsToLean! "cvc5_kind.h"

#guard_msgs(drop info) in #check Kind
#guard_msgs(drop info) in #check Kind.LT
#guard_msgs(drop info) in #check (inferInstance : Inhabited Kind)
#guard_msgs(drop info) in #check (inferInstance : Repr Kind)
#guard_msgs(drop info) in #check (inferInstance : BEq Kind)
#guard_msgs(drop info) in #check (inferInstance : Hashable Kind)

#guard_msgs(drop info) in #check SortKind
#guard_msgs(drop info) in #check SortKind.BITVECTOR_SORT
#guard_msgs(drop info) in #check (inferInstance : Inhabited SortKind)
#guard_msgs(drop info) in #check (inferInstance : Repr SortKind)
#guard_msgs(drop info) in #check (inferInstance : BEq SortKind)
#guard_msgs(drop info) in #check (inferInstance : Hashable SortKind)

namespace Kind

@[extern "kind_toString"]
protected opaque toString : Kind → String

instance : ToString Kind := ⟨Kind.toString⟩

end Kind

namespace SortKind

@[extern "sortKind_toString"]
protected opaque toString : SortKind → String

instance : ToString SortKind := ⟨SortKind.toString⟩

end SortKind

end cvc5
