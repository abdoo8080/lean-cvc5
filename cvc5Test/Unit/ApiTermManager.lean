import cvc5Test.Init

/-! # TODO

- only covers tests up to datatype/uninterpreted sorts checks (exclusive)

  <https://github.com/cvc5/cvc5/blob/3759dab95085f510833820b9f98ee9e5c6e122f8/test/unit/api/c/capi_term_manager_black.cpp#L58>

-/
namespace cvc5.Test

test! do
  let _ ← cvc5.getBooleanSort

test! do
  let _ ← cvc5.getIntegerSort

test! do
  let _ ← cvc5.getRealSort

test! do
  let _ ← cvc5.getRegExpSort

test! do
  let _ ← cvc5.getStringSort

test! do
  let _ ← cvc5.getRoundingModeSort

test! do
  let boolSort ← cvc5.getBooleanSort
  let intSort ← cvc5.getIntegerSort
  let realSort ← cvc5.getRealSort
  let bvSort ← cvc5.mkBitVectorSort 32

  let size ←
    bvSort.getBitVectorSize
    |> assertOk
  assertEq size 32

  cvc5.mkArraySort boolSort boolSort
  |> assertOkDiscard
  cvc5.mkArraySort intSort intSort
  |> assertOkDiscard
  cvc5.mkArraySort realSort realSort
  |> assertOkDiscard
  cvc5.mkArraySort bvSort bvSort
  |> assertOkDiscard
  cvc5.mkArraySort boolSort intSort
  |> assertOkDiscard
  cvc5.mkArraySort realSort bvSort
  |> assertOkDiscard

  let fpSort ← cvc5.mkFloatingPointSort 3 5
  cvc5.mkArraySort fpSort fpSort
  |> assertOkDiscard
  cvc5.mkArraySort bvSort fpSort
  |> assertOkDiscard
  -- already tested, probably a typo in the original test
  cvc5.mkArraySort boolSort boolSort
  |> assertOkDiscard

  cvc5.mkArraySort (← cvc5.getBooleanSort) (← cvc5.getIntegerSort)
  |> assertOkDiscard

test! do
  cvc5.mkBitVectorSort 32
  |> assertOkDiscard
  cvc5.mkBitVectorSort 0
  |> assertError "invalid argument '0' for 'size', expected size > 0"

-- test! do
--   cvc5.mkFiniteFieldSort 31
--   |> assertOkDiscard
--   cvc5.mkFiniteFieldSort 6
--   |> assertError "invalid argument '6' for 'modulus', expected modulus is prime"

--   cvc5.mkFiniteFieldSort 1100101 2
--   |> assertOkDiscard
--   cvc5.mkFiniteFieldSort 10202 3
--   |> assertOkDiscard
--   cvc5.mkFiniteFieldSort 401 5
--   |> assertOkDiscard
--   cvc5.mkFiniteFieldSortOfString "791a" 11
--   |> assertOkDiscard
--   cvc5.mkFiniteFieldSortOfString "970f" 16
--   |> assertOkDiscard
--   cvc5.mkFiniteFieldSortOfString "8CC5" 16
--   |> assertOkDiscard

--   cvc5.mkFiniteFieldSort 1100100 2
--   |> assertError "invalid argument '1100100' for 'modulus', expected modulus is prime"
--   cvc5.mkFiniteFieldSort 10201 3
--   |> assertError "invalid argument '10201' for 'modulus', expected modulus is prime"
--   cvc5.mkFiniteFieldSort 400 5
--   |> assertError "invalid argument '400' for 'modulus', expected modulus is prime"
--   cvc5.mkFiniteFieldSort 7919 11
--   |> assertError "invalid argument '7919' for 'modulus', expected modulus is prime"
--   cvc5.mkFiniteFieldSortOfString "970e" 16
--   |> assertError "invalid argument '970e' for 'modulus', expected modulus is prime"
--   cvc5.mkFiniteFieldSortOfString "8CC4" 16
--   |> assertError "invalid argument '8CC4' for 'modulus', expected modulus is prime"

test! do
  cvc5.mkFloatingPointSort 4 8
  |> assertOkDiscard

  cvc5.mkFloatingPointSort 0 8
  |> assertError "invalid argument '0' for 'exp', expected exponent size > 1"
  cvc5.mkFloatingPointSort 4 0
  |> assertError "invalid argument '0' for 'sig', expected significand size > 1"
  cvc5.mkFloatingPointSort 1 8
  |> assertError "invalid argument '1' for 'exp', expected exponent size > 1"
  cvc5.mkFloatingPointSort 4 1
  |> assertError "invalid argument '1' for 'sig', expected significand size > 1"



-- /-! # TODO

-- Datatype-related tests

-- - <https://github.com/cvc5/cvc5/blob/0b00421403d4493cc01c1dd4b69269a139cb0bc2/test/unit/api/cpp/api_term_manager_black.cpp#L118-L232>
-- -/


-- test! do
--   let uf ←
--     cvc5.mkUninterpretedSort "u"
--     |> assertOk
--   let int := cvc5.getIntegerSort
--   let funSort ←
--     cvc5.mkFunctionSort #[uf] int
--     |> assertOk

--   -- function arguments are allowed
--   cvc5.mkFunctionSort #[funSort] int
--   |> assertOkDiscard
--   -- non-first-class arguments are not allowed
--   let reSort := cvc5.getRegExpSort
--   cvc5.mkFunctionSort #[reSort] int
--   |> assertError
--     "invalid domain sort in 'sorts' at index 0, expected first-class sort as domain sort"
--   --
--   cvc5.mkFunctionSort #[int] funSort
--   |> assertError
--     "invalid argument '(-> u Int)' for 'codomain', expected non-function sort as codomain sort"
--   --
--   cvc5.mkFunctionSort #[uf, int] int
--   |> assertOkDiscard

--   let funSort2 ←
--     cvc5.mkFunctionSort #[← cvc5.mkUninterpretedSort "u"] cvc5.getBooleanSort
--     |> assertOk
--   --
--   cvc5.mkFunctionSort #[funSort2, uf] int
--   |> assertOkDiscard
--   --
--   cvc5.mkFunctionSort #[int, uf] funSort2
--   |> assertError
--     "invalid argument '(-> u Bool)' for 'codomain', expected non-function sort as codomain sort"

--   let bool := cvc5.getBooleanSort
--   let sorts1 := #[bool, int, int]
--   let sorts2 := #[bool, int]

--   cvc5.mkFunctionSort sorts2 int
--   |> assertOkDiscard
--   cvc5.mkFunctionSort sorts1 int
--   |> assertOkDiscard

--   -- At this point the original test creates a new `TermManager` and checks that some constructors
--   -- fail because the manager is not a singleton anymore. But we don't have that problem.
--   let tm ← TermManager.new
--   cvc5.mkFunctionSort sorts2 int
--   |> assertOkDiscard
--   cvc5.mkFunctionSort #[cvc5.getBooleanSort, cvc5.getIntegerSort] cvc5.getIntegerSort
--   |> assertOkDiscard

-- test! do
--   cvc5.mkParamSort "T"
--   |> assertOkDiscard
--   cvc5.mkParamSort ""
--   |> assertOkDiscard

-- test! do
--   cvc5.mkPredicateSort #[cvc5.getIntegerSort]
--   |> assertOkDiscard
--   cvc5.mkPredicateSort #[]
--   |> assertError
--     "invalid size of argument 'sorts', expected at least one parameter sort for predicate sort"
--   -- function as arguments are allowed
--   let funSort ← cvc5.mkFunctionSort #[← cvc5.mkUninterpretedSort "u"] cvc5.getIntegerSort
--   cvc5.mkPredicateSort #[cvc5.getIntegerSort, funSort]
--   |> assertOkDiscard
--   cvc5.mkPredicateSort #[cvc5.getIntegerSort]
--   |> assertOkDiscard

--   -- At this point the original test creates a new `TermManager` and checks that some constructors
--   -- fail because the manager is not a singleton anymore. But we don't have that problem.
--   let tm ← TermManager.new
--   cvc5.mkPredicateSort #[cvc5.getIntegerSort]
--   |> assertOkDiscard
