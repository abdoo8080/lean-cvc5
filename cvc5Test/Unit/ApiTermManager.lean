import cvc5Test.Init

/-! # TODO

- only covers tests up to datatype/uninterpreted sorts checks (exclusive)

  <https://github.com/cvc5/cvc5/blob/3759dab95085f510833820b9f98ee9e5c6e122f8/test/unit/api/c/capi_term_manager_black.cpp#L58>

-/
namespace cvc5.Test

test! do
  let _ ← getBooleanSort

test! do
  let _ ← getIntegerSort

test! do
  let _ ← getRealSort

test! do
  let _ ← getRegExpSort

test! do
  let _ ← getStringSort

test! do
  let _ ← getRoundingModeSort

test! do
  let boolSort ← getBooleanSort
  let intSort ← getIntegerSort
  let realSort ← getRealSort
  let bvSort ← mkBitVectorSort 32

  let size ←
    bvSort.getBitVectorSize
    |> assertOk
  assertEq size 32

  mkArraySort boolSort boolSort
  |> assertOkDiscard
  mkArraySort intSort intSort
  |> assertOkDiscard
  mkArraySort realSort realSort
  |> assertOkDiscard
  mkArraySort bvSort bvSort
  |> assertOkDiscard
  mkArraySort boolSort intSort
  |> assertOkDiscard
  mkArraySort realSort bvSort
  |> assertOkDiscard

  let fpSort ← mkFloatingPointSort 3 5
  mkArraySort fpSort fpSort
  |> assertOkDiscard
  mkArraySort bvSort fpSort
  |> assertOkDiscard
  -- already tested, probably a typo in the original test
  mkArraySort boolSort boolSort
  |> assertOkDiscard

  mkArraySort (← getBooleanSort) (← getIntegerSort)
  |> assertOkDiscard

test! do
  mkBitVectorSort 32
  |> assertOkDiscard
  mkBitVectorSort 0
  |> assertError "invalid argument '0' for 'size', expected size > 0"

test! do
  mkFiniteFieldSort 31
  |> assertOkDiscard
  mkFiniteFieldSort 6
  |> assertError "invalid argument '6' for 'modulus', expected modulus is prime"

  mkFiniteFieldSort 1100101 2
  |> assertOkDiscard
  mkFiniteFieldSort 10202 3
  |> assertOkDiscard
  mkFiniteFieldSort 401 5
  |> assertOkDiscard
  mkFiniteFieldSortOfString "791a" 11
  |> assertOkDiscard
  mkFiniteFieldSortOfString "970f" 16
  |> assertOkDiscard
  mkFiniteFieldSortOfString "8CC5" 16
  |> assertOkDiscard

  mkFiniteFieldSort 1100100 2
  |> assertError "invalid argument '1100100' for 'modulus', expected modulus is prime"
  mkFiniteFieldSort 10201 3
  |> assertError "invalid argument '10201' for 'modulus', expected modulus is prime"
  mkFiniteFieldSort 400 5
  |> assertError "invalid argument '400' for 'modulus', expected modulus is prime"
  mkFiniteFieldSort 7919 11
  |> assertError "invalid argument '7919' for 'modulus', expected modulus is prime"
  mkFiniteFieldSortOfString "970e" 16
  |> assertError "invalid argument '970e' for 'modulus', expected modulus is prime"
  mkFiniteFieldSortOfString "8CC4" 16
  |> assertError "invalid argument '8CC4' for 'modulus', expected modulus is prime"

test! do
  mkFloatingPointSort 4 8
  |> assertOkDiscard

  mkFloatingPointSort 0 8
  |> assertError "invalid argument '0' for 'exp', expected exponent size > 1"
  mkFloatingPointSort 4 0
  |> assertError "invalid argument '0' for 'sig', expected significand size > 1"
  mkFloatingPointSort 1 8
  |> assertError "invalid argument '1' for 'exp', expected exponent size > 1"
  mkFloatingPointSort 4 1
  |> assertError "invalid argument '1' for 'sig', expected significand size > 1"



/-! # TODO

Datatype-related tests

- <https://github.com/cvc5/cvc5/blob/0b00421403d4493cc01c1dd4b69269a139cb0bc2/test/unit/api/cpp/api_term_manager_black.cpp#L118-L232>
-/


test! do
  let uf ←
    mkUninterpretedSort "u"
    |> assertOk
  let int ← getIntegerSort
  let funSort ←
    mkFunctionSort #[uf] int
    |> assertOk

  -- function arguments are allowed
  mkFunctionSort #[funSort] int
  |> assertOkDiscard
  -- non-first-class arguments are not allowed
  let reSort ← getRegExpSort
  mkFunctionSort #[reSort] int
  |> assertError
    "invalid domain sort in 'sorts' at index 0, expected first-class sort as domain sort"
  --
  mkFunctionSort #[int] funSort
  |> assertError
    "invalid argument '(-> u Int)' for 'codomain', expected non-function sort as codomain sort"
  --
  mkFunctionSort #[uf, int] int
  |> assertOkDiscard

  let funSort2 ←
    mkFunctionSort #[← mkUninterpretedSort "u"] (← getBooleanSort)
    |> assertOk
  --
  mkFunctionSort #[funSort2, uf] int
  |> assertOkDiscard
  --
  mkFunctionSort #[int, uf] funSort2
  |> assertError
    "invalid argument '(-> u Bool)' for 'codomain', expected non-function sort as codomain sort"

  let bool ← getBooleanSort
  let sorts1 := #[bool, int, int]
  let sorts2 := #[bool, int]

  mkFunctionSort sorts2 int
  |> assertOkDiscard
  mkFunctionSort sorts1 int
  |> assertOkDiscard

  -- At this point the original test creates a new `TermManager` and checks that some constructors
  -- fail because the manager is not a singleton anymore. But we don't have that problem.

test! do
  mkParamSort "T"
  |> assertOkDiscard
  mkParamSort ""
  |> assertOkDiscard

test! do
  mkPredicateSort #[← getIntegerSort]
  |> assertOkDiscard
  mkPredicateSort #[]
  |> assertError
    "invalid size of argument 'sorts', expected at least one parameter sort for predicate sort"
  -- function as arguments are allowed
  let funSort ← mkFunctionSort #[← mkUninterpretedSort "u"] (← getIntegerSort)
  mkPredicateSort #[← getIntegerSort, funSort]
  |> assertOkDiscard
  mkPredicateSort #[← getIntegerSort]
  |> assertOkDiscard

  -- At this point the original test creates a new `TermManager` and checks that some constructors
  -- fail because the manager is not a singleton anymore. But we don't have that problem.
