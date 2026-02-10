import cvc5Test.Init

/-! # Black box testing of the term manager

- <https://github.com/cvc5/cvc5/blob/e342ecb325520619db2a1f49e95f96ebca8029f2/test/unit/api/cpp/api_term_manager_black.cpp>
-/
namespace cvc5.Test

test![TestApiBlackTermManager, getBooleanSort] tm => do
  tm.getBooleanSort |> assertOkDiscard

test![TestApiBlackTermManager, getIntegerSort] tm => do
  tm.getIntegerSort |> assertOkDiscard

test![TestApiBlackTermManager, getRealSort] tm => do
  tm.getRealSort |> assertOkDiscard

test![TestApiBlackTermManager, getRegExpSort] tm => do
  tm.getRegExpSort |> assertOkDiscard

test![TestApiBlackTermManager, getStringSort] tm => do
  tm.getStringSort |> assertOkDiscard

test![TestApiBlackTermManager, getRoundingModeSort] tm => do
  tm.getRoundingModeSort |> assertOkDiscard

test![TestApiBlackTermManager, mkArraySort] tm => do
  let boolSort ← tm.getBooleanSort
  let intSort ← tm.getIntegerSort
  let realSort ← tm.getRealSort
  let bvSort ← tm.mkBitVectorSort 32

  let size ← bvSort.getBitVectorSize |> assertOk
  assertEq size 32

  tm.mkArraySort boolSort boolSort |> assertOkDiscard
  tm.mkArraySort intSort intSort |> assertOkDiscard
  tm.mkArraySort realSort realSort |> assertOkDiscard
  tm.mkArraySort bvSort bvSort |> assertOkDiscard
  tm.mkArraySort boolSort intSort |> assertOkDiscard
  tm.mkArraySort realSort bvSort |> assertOkDiscard

  let fpSort ← tm.mkFloatingPointSort 3 5
  tm.mkArraySort fpSort fpSort |> assertOkDiscard
  tm.mkArraySort bvSort fpSort |> assertOkDiscard
  tm.mkArraySort boolSort boolSort |> assertOkDiscard

  tm.mkArraySort (← tm.getBooleanSort) (← tm.getIntegerSort) |> assertOkDiscard

test![TestApiBlackTermManager, mkBitVectorSort] tm => do
  tm.mkBitVectorSort 32 |> assertOkDiscard
  tm.mkBitVectorSort 0 |> assertError "invalid argument '0' for 'size', expected size > 0"

test![TestApiBlackTermManager, mkFiniteFieldSort] tm => do
  tm.mkFiniteFieldSort 31 |> assertOkDiscard
  tm.mkFiniteFieldSort 6 |> assertError
    "invalid argument '6' for 'modulus', expected modulus is prime"

  tm.mkFiniteFieldSort 1100101 2 |> assertOkDiscard
  tm.mkFiniteFieldSort 10202 3 |> assertOkDiscard
  tm.mkFiniteFieldSort 401 5 |> assertOkDiscard
  tm.mkFiniteFieldSortOfString "791a" 11 |> assertOkDiscard
  tm.mkFiniteFieldSortOfString "970f" 16 |> assertOkDiscard
  tm.mkFiniteFieldSortOfString "8CC5" 16 |> assertOkDiscard

  tm.mkFiniteFieldSort 1100100 2 |> assertError
    "invalid argument '1100100' for 'modulus', expected modulus is prime"
  tm.mkFiniteFieldSort 10201 3 |> assertError
    "invalid argument '10201' for 'modulus', expected modulus is prime"
  tm.mkFiniteFieldSort 400 5 |> assertError
    "invalid argument '400' for 'modulus', expected modulus is prime"
  tm.mkFiniteFieldSort 7919 11 |> assertError
    "invalid argument '7919' for 'modulus', expected modulus is prime"
  tm.mkFiniteFieldSortOfString "970e" 16 |> assertError
    "invalid argument '970e' for 'modulus', expected modulus is prime"
  tm.mkFiniteFieldSortOfString "8CC4" 16 |> assertError
    "invalid argument '8CC4' for 'modulus', expected modulus is prime"

test![TestApiBlackTermManager, mkFloatingPointSort] tm => do
  tm.mkFloatingPointSort 4 8 |> assertOkDiscard

  tm.mkFloatingPointSort 0 8 |> assertError
    "invalid argument '0' for 'exp', expected exponent size > 1"
  tm.mkFloatingPointSort 4 0 |> assertError
    "invalid argument '0' for 'sig', expected significand size > 1"
  tm.mkFloatingPointSort 1 8 |> assertError
    "invalid argument '1' for 'exp', expected exponent size > 1"
  tm.mkFloatingPointSort 4 1 |> assertError
    "invalid argument '1' for 'sig', expected significand size > 1"

test![TestApiBlackTermManager, mkDatatypeSort] tm => do
  let int ← tm.getIntegerSort

  let _scope ← do
    let mut dtSpec ← tm.mkDatatypeDecl "list"
    let mut consSpec ← tm.mkDatatypeConstructorDecl "cons"
    consSpec ← consSpec.addSelector "head" int
    dtSpec ← dtSpec.addConstructor consSpec
    let nilSpec ← tm.mkDatatypeConstructorDecl "nil"
    dtSpec ← dtSpec.addConstructor nilSpec
    tm.mkDatatypeSort dtSpec |> assertOkDiscard

    tm.mkDatatypeSort dtSpec |> assertError
      "Given datatype declaration is already resolved \
      (has already been used to create a datatype sort)"
    tm.mkDatatypeSort dtSpec |> assertError
      "Given datatype declaration is already resolved \
      (has already been used to create a datatype sort)"

  let badDtSpec ← tm.mkDatatypeDecl "list"
  tm.mkDatatypeSort badDtSpec |> assertError
    "invalid argument 'DATATYPE list = \n END;\n' for 'dtypedecl', \
    expected a datatype declaration with at least one constructor"

  let _scope ← do
    let tm' ← TermManager.new
    let mut dtSpec' ← tm'.mkDatatypeDecl "list"
    let mut consSpec' ← tm'.mkDatatypeConstructorDecl "cons"
    consSpec' ← consSpec'.addSelector "head" (← tm'.getIntegerSort)
    dtSpec' ← dtSpec'.addConstructor consSpec'
    let nilSpec' ← tm'.mkDatatypeConstructorDecl "nil"
    dtSpec' ← dtSpec'.addConstructor nilSpec'
    tm.mkDatatypeSort dtSpec' |> assertError
      "Given datatype declaration is not associated with this term manager"

test![TestApiBlackTermManager, mkDatatypeSorts] tm => do
  let int ← tm.getIntegerSort
  let bool ← tm.getBooleanSort

  let _scope ← do
    let mut dt1Spec ← tm.mkDatatypeDecl "list1"
    let mut cons1Spec ← tm.mkDatatypeConstructorDecl "cons1"
    cons1Spec ← cons1Spec.addSelector "head1" int
    dt1Spec ← dt1Spec.addConstructor cons1Spec
    let nil1Spec ← tm.mkDatatypeConstructorDecl "nil1"
    dt1Spec ← dt1Spec.addConstructor nil1Spec
    let mut dt2Spec ← tm.mkDatatypeDecl "list2"
    let mut cons2Spec ← tm.mkDatatypeConstructorDecl "cons2"
    cons2Spec ← cons2Spec.addSelector "head2" int
    dt2Spec ← dt2Spec.addConstructor cons2Spec
    let nil2Spec ← tm.mkDatatypeConstructorDecl "nil2"
    dt2Spec ← dt2Spec.addConstructor nil2Spec
    let decls := #[dt1Spec, dt2Spec]
    tm.mkDatatypeSorts decls |> assertOkDiscard

    tm.mkDatatypeSorts decls |> assertError
      "Given datatype declaration is already resolved \
      (has already been used to create a datatype sort)"
    tm.mkDatatypeSorts decls |> assertError
      "Given datatype declaration is already resolved \
      (has already been used to create a datatype sort)"

  let badDtSpec ← tm.mkDatatypeDecl "list"
  let badDecls := #[badDtSpec]
  tm.mkDatatypeSorts badDecls |> assertError
    "invalid datatype declaration in 'dtypedecls' at index 0, \
    expected a datatype declaration with at least one constructor"

  -- with unresolved sorts
  let unresList ← tm.mkUnresolvedDatatypeSort "ulist"
  let mut ulist ← tm.mkDatatypeDecl "ulist"
  let mut uconsSpec ← tm.mkDatatypeConstructorDecl "ucons"
  uconsSpec ← uconsSpec.addSelector "car" unresList
  uconsSpec ← uconsSpec.addSelector "cdr" unresList
  ulist ← ulist.addConstructor uconsSpec
  let unilSpec ← tm.mkDatatypeConstructorDecl "unil"
  ulist ← ulist.addConstructor unilSpec
  let udecls := #[ulist]
  tm.mkDatatypeSorts udecls |> assertOkDiscard

  tm.mkDatatypeSorts udecls |> assertError
    "Given datatype declaration is already resolved \
    (has already been used to create a datatype sort)"
  tm.mkDatatypeSorts udecls |> assertError
    "Given datatype declaration is already resolved \
    (has already been used to create a datatype sort)"

  -- mutually recursive with unresolved parameterized sorts
  let p0 ← tm.mkParamSort "p0"
  let p1 ← tm.mkParamSort "p1"
  let u0 ← tm.mkUnresolvedDatatypeSort "dt0" 1
  let u1 ← tm.mkUnresolvedDatatypeSort "dt1" 1
  let mut dt0Spec ← tm.mkDatatypeDecl "dt0" #[p0]
  let mut dt1Spec ← tm.mkDatatypeDecl "dt1" #[p1]
  let mut ctor0Spec ← tm.mkDatatypeConstructorDecl "c0"
  ctor0Spec ← u1.instantiate #[p0] >>= ctor0Spec.addSelector "s0"
  let mut ctor1Spec ← tm.mkDatatypeConstructorDecl "c1"
  ctor1Spec ← u0.instantiate #[p1] >>= ctor1Spec.addSelector "s1"
  dt0Spec ← dt0Spec.addConstructor ctor0Spec
  dt1Spec ← dt1Spec.addConstructor ctor1Spec
  dt1Spec ← tm.mkDatatypeConstructorDecl "nil" >>= dt1Spec.addConstructor
  let dtSorts ← tm.mkDatatypeSorts #[dt0Spec, dt1Spec]
  let isort1 ← dtSorts[1]!.instantiate #[bool]
  let t1 ← tm.mkConst isort1 "t"
  let t0 ← do
    let selector ← t1.getSort.getDatatype!.getSelector "s1" >>= DatatypeSelector.getTerm
    tm.mkTerm Kind.APPLY_SELECTOR #[selector, t1]
  assertEq t0.getSort (dtSorts[0]!.instantiate! #[bool])

  let _scope ← do
    let tm' ← TermManager.new
    let int' ← tm'.getIntegerSort
    let mut dt1Spec' ← tm'.mkDatatypeDecl "list1"
    let mut cons1Spec' ← tm'.mkDatatypeConstructorDecl "cons1"
    cons1Spec' ← cons1Spec'.addSelector "head1" int'
    dt1Spec' ← dt1Spec'.addConstructor cons1Spec'
    let nil1Spec' ← tm'.mkDatatypeConstructorDecl "nil1"
    dt1Spec' ← dt1Spec'.addConstructor nil1Spec'
    let mut dt2Spec' ← tm'.mkDatatypeDecl "list2"
    let mut cons2Spec' ← tm'.mkDatatypeConstructorDecl "cons2"
    cons2Spec' ← cons2Spec'.addSelector "head2" int'
    dt2Spec' ← dt2Spec'.addConstructor cons2Spec'
    let nil2Spec ← tm'.mkDatatypeConstructorDecl "nil2"
    dt2Spec' ← dt2Spec'.addConstructor nil2Spec
    let decls' := #[dt1Spec', dt2Spec']
    tm.mkDatatypeSorts decls' |> assertError
      "invalid datatype declaration in 'dtypedecls' at index 0, \
      expected a datatype declaration associated with this term manager"


test![TestApiBlackTermManager, mkFunctionSort] tm => do
  let uf ← tm.mkUninterpretedSort "u" |> assertOk
  let int ← tm.getIntegerSort
  let funSort ← tm.mkFunctionSort #[uf] int |> assertOk

  -- function arguments are allowed
  tm.mkFunctionSort #[funSort] int |> assertOkDiscard
  -- non-first-class arguments are not allowed
  tm.mkFunctionSort #[int] funSort |> assertError
    "invalid argument '(-> u Int)' for 'codomain', expected non-function sort as codomain sort"
  --
  tm.mkFunctionSort #[uf, int] int |> assertOkDiscard

  let funSort2 ← tm.mkFunctionSort #[← tm.mkUninterpretedSort "u"] (← tm.getBooleanSort) |> assertOk
  --
  tm.mkFunctionSort #[funSort2, uf] int |> assertOkDiscard
  --
  tm.mkFunctionSort #[int, uf] funSort2 |> assertError
    "invalid argument '(-> u Bool)' for 'codomain', expected non-function sort as codomain sort"

  let bool ← tm.getBooleanSort
  let sorts1 := #[bool, int, int]
  let sorts2 := #[bool, int]

  tm.mkFunctionSort sorts2 int |> assertOkDiscard
  tm.mkFunctionSort sorts1 int |> assertOkDiscard

  let tm' ← TermManager.new
  let bool' ← tm'.getBooleanSort
  let int' ← tm'.getIntegerSort
  tm'.mkFunctionSort sorts2 int' |> assertError
    "invalid domain sort in 'sorts' at index 0, expected a sort associated with this term manager"
  tm'.mkFunctionSort #[bool', int'] int |> assertError
    "Given sort is not associated with this term manager"

test![TestApiBlackTermManager, mkParamSort] tm => do
  tm.mkParamSort "T" |> assertOkDiscard
  tm.mkParamSort "" |> assertOkDiscard

test![TestApiBlackTermManager, mkPredicateSort] tm => do
  tm.mkPredicateSort #[← tm.getIntegerSort] |> assertOkDiscard
  tm.mkPredicateSort #[] |> assertError
    "invalid size of argument 'sorts', expected at least one parameter sort for predicate sort"
  -- function as arguments are allowed
  let funSort ← tm.mkFunctionSort #[← tm.mkUninterpretedSort "u"] (← tm.getIntegerSort)
  tm.mkPredicateSort #[← tm.getIntegerSort, funSort] |> assertOkDiscard
  tm.mkPredicateSort #[← tm.getIntegerSort] |> assertOkDiscard

  let tm' ← TermManager.new
  tm'.mkPredicateSort #[← tm.getIntegerSort] |> assertError
    "invalid domain sort in 'sorts' at index 0, expected a sort associated with this term manager"
