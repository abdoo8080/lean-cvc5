/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Adrien Champion
-/

import cvc5Test.Init

/-!
https://github.com/abdoo8080/lean-cvc5/issues/33
-/

namespace cvc5.Test

test![Issue33, mkRecordSort] tm => do
  let fields := #[ ("field1", ← tm.getIntegerSort), ("field2", ← tm.getBooleanSort) ]
  tm.mkRecordSort fields |> assertOkDiscard
  tm.mkRecordSort fields |> assertOkDiscard
