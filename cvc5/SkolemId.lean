/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import cvc5.Autogen

namespace cvc5

cppEnumsToLean! "cvc5_skolem_id.h"

#guard_msgs(drop info) in #check SkolemId
#guard_msgs(drop info) in #check SkolemId.STRINGS_OCCUR_INDEX_RE
#guard_msgs(drop info) in #check (inferInstance : Inhabited SkolemId)
#guard_msgs(drop info) in #check (inferInstance : Repr SkolemId)
#guard_msgs(drop info) in #check (inferInstance : BEq SkolemId)
#guard_msgs(drop info) in #check (inferInstance : Hashable SkolemId)

namespace SkolemId

@[extern "skolemId_toString"]
protected opaque toString : SkolemId → String

instance : ToString SkolemId := ⟨SkolemId.toString⟩

end SkolemId

end cvc5
