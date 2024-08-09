import Cvc5Test.Init

/-! # TODO

- only covers tests up to datatype checks (exclusive)

  <https://github.com/cvc5/cvc5/blob/0b00421403d4493cc01c1dd4b69269a139cb0bc2/test/unit/api/cpp/api_term_manager_black.cpp#L118>

-/
namespace cvc5.Test

test! tm => do
  let _ := tm.getBooleanSort

test! tm => do
  let _ := tm.getIntegerSort

test! tm => do
  let _ := tm.getRealSort

test! tm => do
  let _ := tm.getRegExpSort

test! tm => do
  let _ := tm.getStringSort

test! tm => do
  let _ := tm.getRoundingModeSort

test! tm => do
  let boolSort := tm.getBooleanSort
  let intSort := tm.getIntegerSort
  let realSort := tm.getRealSort
  let bvSort := tm.mkBitVectorSort 32

  tm.mkArraySort boolSort boolSort
  |> assertOkDiscard
  tm.mkArraySort intSort intSort
  |> assertOkDiscard
  tm.mkArraySort realSort realSort
  |> assertOkDiscard
  tm.mkArraySort bvSort bvSort
  |> assertOkDiscard
  tm.mkArraySort boolSort intSort
  |> assertOkDiscard
  tm.mkArraySort realSort bvSort
  |> assertOkDiscard

  let fpSort ← tm.mkFloatingPointSort 3 5
  tm.mkArraySort fpSort fpSort
  |> assertOkDiscard
  tm.mkArraySort bvSort fpSort
  |> assertOkDiscard
  -- already tested, probably a typo in the original test
  tm.mkArraySort boolSort boolSort
  |> assertOkDiscard

  tm.mkArraySort tm.getBooleanSort tm.getIntegerSort
  |> assertOkDiscard

/-- error: unsolved goals
tm : TermManager
x✝ : Sort := tm.mkBitVectorSort 32 ⋯
⊢ False
---
info:
-/
test! tm => do
  let _ := tm.mkBitVectorSort 32
  let _ := tm.mkBitVectorSort 0 -- illegal `0` size

test! tm => do
  tm.mkFiniteFieldSort 31
  |> assertOkDiscard
  tm.mkFiniteFieldSort 6
  |> assertCvc5Error "invalid argument '6' for 'modulus', expected modulus is prime"

  tm.mkFiniteFieldSort 1100101 2
  |> assertOkDiscard
  tm.mkFiniteFieldSort 10202 3
  |> assertOkDiscard
  tm.mkFiniteFieldSort 401 5
  |> assertOkDiscard
  tm.mkFiniteFieldSortOfString "791a" 11
  |> assertOkDiscard
  tm.mkFiniteFieldSortOfString "970f" 16
  |> assertOkDiscard
  tm.mkFiniteFieldSortOfString "8CC5" 16
  |> assertOkDiscard

  tm.mkFiniteFieldSort 1100100 2
  |> assertCvc5Error "invalid argument '1100100' for 'modulus', expected modulus is prime"
  tm.mkFiniteFieldSort 10201 3
  |> assertCvc5Error "invalid argument '10201' for 'modulus', expected modulus is prime"
  tm.mkFiniteFieldSort 400 5
  |> assertCvc5Error "invalid argument '400' for 'modulus', expected modulus is prime"
  tm.mkFiniteFieldSort 7919 11
  |> assertCvc5Error "invalid argument '7919' for 'modulus', expected modulus is prime"
  tm.mkFiniteFieldSortOfString "970e" 16
  |> assertCvc5Error "invalid argument '970e' for 'modulus', expected modulus is prime"
  tm.mkFiniteFieldSortOfString "8CC4" 16
  |> assertCvc5Error "invalid argument '8CC4' for 'modulus', expected modulus is prime"

/--
error: unsolved goals
tm : TermManager
x✝ : PUnit
⊢ False
---
error: unsolved goals
tm : TermManager
x✝¹ x✝ : PUnit
⊢ False
---
error: unsolved goals
tm : TermManager
x✝² x✝¹ x✝ : PUnit
⊢ False
---
error: unsolved goals
tm : TermManager
x✝³ x✝² x✝¹ x✝ : PUnit
⊢ False
---
info:
-/
test! tm => do
  tm.mkFloatingPointSort 4 8
  |> assertOkDiscard
  tm.mkFloatingPointSort 0 8
  |> assertCvc5Error "invalid argument '0' for 'exp', expected exponent size > 1"
  tm.mkFloatingPointSort 4 0
  |> assertCvc5Error "invalid argument '0' for 'sig', expected significand size > 1"
  tm.mkFloatingPointSort 1 8
  |> assertCvc5Error "invalid argument '1' for 'exp', expected exponent size > 1"
  tm.mkFloatingPointSort 4 1
  |> assertCvc5Error "invalid argument '1' for 'sig', expected significand size > 1"
