/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/



namespace cvc5.Test

/-- Crashes with an explanation if `expected ≠ value`. -/
def check! [Repr α] [BEq α]
  (expected value : α)
: IO Unit :=
  if expected != value then do
    println! "expected `{repr expected}`, got `{repr value}`"
    panic! "check failed"
  else return ()

end cvc5.Test
