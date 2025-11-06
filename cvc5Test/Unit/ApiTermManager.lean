import cvc5Test.Init

/-! # TODO

- only covers tests up to datatype/uninterpreted sorts checks (exclusive)

  <https://github.com/cvc5/cvc5/blob/3759dab95085f510833820b9f98ee9e5c6e122f8/test/unit/api/c/capi_term_manager_black.cpp#L58>

-/
namespace cvc5.Test

test! tm => do
  let _ ← tm.getBooleanSort

test! tm => do
  let _ ← tm.getIntegerSort

test! tm => do
  let _ ← tm.getRealSort

test! tm => do
  let _ ← tm.getRegExpSort

test! tm => do
  let _ ← tm.getStringSort

test! tm => do
  let _ ← tm.getRoundingModeSort

test! tm => do
  let boolSort ← tm.getBooleanSort
  let intSort ← tm.getIntegerSort
  let realSort ← tm.getRealSort
  let bvSort ← tm.mkBitVectorSort 32

  let size ←
    bvSort.getBitVectorSize
    |> assertOk
  assertEq size 32

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

  tm.mkArraySort (← tm.getBooleanSort) (← tm.getIntegerSort)
  |> assertOkDiscard

test! tm => do
  tm.mkBitVectorSort 32
  |> assertOkDiscard
  tm.mkBitVectorSort 0
  |> assertError "invalid argument '0' for 'size', expected size > 0"

test! tm => do
  tm.mkFiniteFieldSort 31
  |> assertOkDiscard
  tm.mkFiniteFieldSort 6
  |> assertError "invalid argument '6' for 'modulus', expected modulus is prime"

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
  |> assertError "invalid argument '1100100' for 'modulus', expected modulus is prime"
  tm.mkFiniteFieldSort 10201 3
  |> assertError "invalid argument '10201' for 'modulus', expected modulus is prime"
  tm.mkFiniteFieldSort 400 5
  |> assertError "invalid argument '400' for 'modulus', expected modulus is prime"
  tm.mkFiniteFieldSort 7919 11
  |> assertError "invalid argument '7919' for 'modulus', expected modulus is prime"
  tm.mkFiniteFieldSortOfString "970e" 16
  |> assertError "invalid argument '970e' for 'modulus', expected modulus is prime"
  tm.mkFiniteFieldSortOfString "8CC4" 16
  |> assertError "invalid argument '8CC4' for 'modulus', expected modulus is prime"

test! tm => do
  tm.mkFloatingPointSort 4 8
  |> assertOkDiscard

  tm.mkFloatingPointSort 0 8
  |> assertError "invalid argument '0' for 'exp', expected exponent size > 1"
  tm.mkFloatingPointSort 4 0
  |> assertError "invalid argument '0' for 'sig', expected significand size > 1"
  tm.mkFloatingPointSort 1 8
  |> assertError "invalid argument '1' for 'exp', expected exponent size > 1"
  tm.mkFloatingPointSort 4 1
  |> assertError "invalid argument '1' for 'sig', expected significand size > 1"



/-! # TODO

Datatype-related tests

- <https://github.com/cvc5/cvc5/blob/0b00421403d4493cc01c1dd4b69269a139cb0bc2/test/unit/api/cpp/api_term_manager_black.cpp#L118-L232>
-/


test! tm => do
  let uf ←
    tm.mkUninterpretedSort "u"
    |> assertOk
  let int ← tm.getIntegerSort
  let funSort ←
    tm.mkFunctionSort #[uf] int
    |> assertOk

  -- function arguments are allowed
  tm.mkFunctionSort #[funSort] int
  |> assertOkDiscard
  -- non-first-class arguments are not allowed
  let reSort ← tm.getRegExpSort
  tm.mkFunctionSort #[reSort] int
  |> assertError
    "invalid domain sort in 'sorts' at index 0, expected first-class sort as domain sort"
  --
  tm.mkFunctionSort #[int] funSort
  |> assertError
    "invalid argument '(-> u Int)' for 'codomain', expected non-function sort as codomain sort"
  --
  tm.mkFunctionSort #[uf, int] int
  |> assertOkDiscard

  let funSort2 ←
    tm.mkFunctionSort #[← tm.mkUninterpretedSort "u"] (← tm.getBooleanSort)
    |> assertOk
  --
  tm.mkFunctionSort #[funSort2, uf] int
  |> assertOkDiscard
  --
  tm.mkFunctionSort #[int, uf] funSort2
  |> assertError
    "invalid argument '(-> u Bool)' for 'codomain', expected non-function sort as codomain sort"

  let bool ← tm.getBooleanSort
  let sorts1 := #[bool, int, int]
  let sorts2 := #[bool, int]

  tm.mkFunctionSort sorts2 int
  |> assertOkDiscard
  tm.mkFunctionSort sorts1 int
  |> assertOkDiscard

  -- At this point the original test creates a new `TermManager` and checks that some constructors
  -- fail because the manager is not a singleton anymore. But we don't have that problem.

test! tm => do
  tm.mkParamSort "T"
  |> assertOkDiscard
  tm.mkParamSort ""
  |> assertOkDiscard

test! tm => do
  tm.mkPredicateSort #[← tm.getIntegerSort]
  |> assertOkDiscard
  tm.mkPredicateSort #[]
  |> assertError
    "invalid size of argument 'sorts', expected at least one parameter sort for predicate sort"
  -- function as arguments are allowed
  let funSort ← tm.mkFunctionSort #[← tm.mkUninterpretedSort "u"] (← tm.getIntegerSort)
  tm.mkPredicateSort #[← tm.getIntegerSort, funSort]
  |> assertOkDiscard
  tm.mkPredicateSort #[← tm.getIntegerSort]
  |> assertOkDiscard

  -- At this point the original test creates a new `TermManager` and checks that some constructors
  -- fail because the manager is not a singleton anymore. But we don't have that problem.
