/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import cvc5.Op.Defs
import cvc5.Term.Defs



namespace cvc5.Op


@[extern "op_get"]
protected opaque get : (op : Op) → Fin op.getNumIndices → Term

instance : GetElem Op Nat Term fun op i => i < op.getNumIndices where
  getElem op i h := op.get ⟨i, h⟩
