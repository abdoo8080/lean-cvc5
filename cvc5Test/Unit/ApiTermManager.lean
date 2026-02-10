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

test![TestApiBlackTermManager, mkRecordSort] tm => do
  let bool ← tm.getBooleanSort
  let int ← tm.getIntegerSort
  let bv ← tm.mkBitVectorSort 8
  let fields := #[ ("b", bool), ("bv", bv), ("i", int) ]
  let empty := #[]
  tm.mkRecordSort fields |> assertOkDiscard
  tm.mkRecordSort empty |> assertOkDiscard
  let recSort ← tm.mkRecordSort fields
  recSort.getDatatype |> assertOkDiscard
  tm.mkRecordSort fields |> assertOkDiscard

  let tm' ← TermManager.new
  tm'.mkRecordSort
    #[ ("b", ← tm'.getBooleanSort), ("bv", ← tm.mkBitVectorSort 8), ("b", ← tm'.getIntegerSort) ]
  |> assertError
    "invalid sort in 'fields' at index 1, expected a sort associated with this term manager"

test![TestApiBlackTermManager, mkSetSort] tm => do
  tm.getBooleanSort >>= tm.mkSetSort |> assertOkDiscard
  tm.getIntegerSort >>= tm.mkSetSort |> assertOkDiscard
  tm.mkBitVectorSort 4 >>= tm.mkSetSort |> assertOkDiscard
  tm.mkBitVectorSort 4 >>= tm.mkSetSort |> assertOkDiscard
  let tm' ← TermManager.new
  tm'.getBooleanSort >>= tm.mkSetSort |> assertError
    "Given sort is not associated with this term manager"

test![TestApiBlackTermManager, mkBagSort] tm => do
  tm.getBooleanSort >>= tm.mkBagSort |> assertOkDiscard
  tm.getIntegerSort >>= tm.mkBagSort |> assertOkDiscard
  tm.mkBitVectorSort 4 >>= tm.mkBagSort |> assertOkDiscard
  tm.mkBitVectorSort 4 >>= tm.mkBagSort |> assertOkDiscard
  let tm' ← TermManager.new
  tm'.getBooleanSort >>= tm.mkBagSort |> assertError
    "Given sort is not associated with this term manager"

test![TestApiBlackTermManager, mkSequenceSort] tm => do
  let bool ← tm.getBooleanSort
  let int ← tm.getIntegerSort
  tm.mkSequenceSort bool |> assertOkDiscard
  tm.mkSequenceSort int >>= tm.mkSequenceSort |> assertOkDiscard
  tm.mkSequenceSort int |> assertOkDiscard
  let tm' ← TermManager.new
  tm'.getBooleanSort >>= tm.mkSequenceSort |> assertError
    "Given sort is not associated with this term manager"

test![TestApiBlackTermManager, mkAbstractSort] tm => do
  tm.mkAbstractSort SortKind.ARRAY_SORT |> assertOkDiscard
  tm.mkAbstractSort SortKind.BITVECTOR_SORT |> assertOkDiscard
  tm.mkAbstractSort SortKind.TUPLE_SORT |> assertOkDiscard
  tm.mkAbstractSort SortKind.SET_SORT |> assertOkDiscard
  tm.mkAbstractSort SortKind.BOOLEAN_SORT |> assertError
    "cannot construct abstract type for kind BOOLEAN_SORT"

test![TestApiBlackTermManager, mkUninterpretedSort] tm => do
  tm.mkUninterpretedSort "u" |> assertOkDiscard
  tm.mkUninterpretedSort "" |> assertOkDiscard

test![TestApiBlackTermManager, mkUnresolvedDatatypeSort] tm => do
  tm.mkUnresolvedDatatypeSort "u" |> assertOkDiscard
  tm.mkUnresolvedDatatypeSort "u" 1 |> assertOkDiscard
  tm.mkUnresolvedDatatypeSort "" |> assertOkDiscard
  tm.mkUnresolvedDatatypeSort "" 1 |> assertOkDiscard

test![TestApiBlackTermManager, mkUninterpretedSortConstructorSort] tm => do
  tm.mkUninterpretedSortConstructorSort 2 "s" |> assertOkDiscard
  tm.mkUninterpretedSortConstructorSort 2 "" |> assertOkDiscard
  tm.mkUninterpretedSortConstructorSort 0 |> assertError
    "invalid argument '0' for 'arity', expected an arity > 0"

test![TestApiBlackTermManager, mkTupleSort] tm => do
  let int ← tm.getIntegerSort
  tm.mkTupleSort #[int] |> assertOkDiscard
  let funSort ← tm.mkFunctionSort #[ ← tm.mkUninterpretedSort "u"] int
  tm.mkTupleSort #[int, funSort] |> assertOkDiscard
  tm.mkTupleSort #[int] |> assertOkDiscard
  let tm' ← TermManager.new
  tm.mkTupleSort #[← tm'.getBooleanSort] |> assertError
    "invalid domain sort in 'sorts' at index 0, expected a sort associated with this term manager"

test![TestApiBlackTermManager, mkNullableSort] tm => do
  tm.getIntegerSort >>= tm.mkNullableSort |> assertOkDiscard
  tm.getIntegerSort >>= tm.mkNullableSort |> assertOkDiscard
  let tm' ← TermManager.new
  tm'.getIntegerSort >>= tm.mkNullableSort |> assertError
    "Given sort is not associated with this term manager"

test![TestApiBlackTermManager, mkBitVector] tm => do
  tm.mkBitVector 8 2 |> assertOkDiscard
  tm.mkBitVector 32 2 |> assertOkDiscard
  tm.mkBitVectorOfString 8 "-1111111" 2 |> assertOkDiscard
  tm.mkBitVectorOfString 8 "0101" 2 |> assertOkDiscard
  tm.mkBitVectorOfString 8 "00000101" 2 |> assertOkDiscard
  tm.mkBitVectorOfString 8 "-127" 10 |> assertOkDiscard
  tm.mkBitVectorOfString 8 "255" 10 |> assertOkDiscard
  tm.mkBitVectorOfString 8 "-7f" 16 |> assertOkDiscard
  tm.mkBitVectorOfString 8 "a0" 16 |> assertOkDiscard

  tm.mkBitVector 0 2 |> assertError
    "invalid argument '0' for 'size', expected a bit-width > 0"
  tm.mkBitVectorOfString 0 "-127" 10 |> assertError
    "invalid argument '0' for 'size', expected a bit-width > 0"
  tm.mkBitVectorOfString 0 "a0" 16 |> assertError
    "invalid argument '0' for 'size', expected a bit-width > 0"

  tm.mkBitVectorOfString 8 "" 2 |> assertError
    "invalid argument '' for 's', expected a non-empty string"

  tm.mkBitVectorOfString 8 "101" 5 |> assertError
    "invalid argument '5' for 'base', expected base 2, 10, or 16"
  tm.mkBitVectorOfString 8 "128" 11 |> assertError
    "invalid argument '11' for 'base', expected base 2, 10, or 16"
  tm.mkBitVectorOfString 8 "a0" 21 |> assertError
    "invalid argument '21' for 'base', expected base 2, 10, or 16"

  tm.mkBitVectorOfString 8 "-11111111" 2 |> assertError
    "overflow in bit-vector construction \
    (specified bit-vector size 8 too small to hold value -11111111)"
  tm.mkBitVectorOfString 8 "101010101" 2 |> assertError
    "overflow in bit-vector construction \
    (specified bit-vector size 8 too small to hold value 101010101)"
  tm.mkBitVectorOfString 8 "-256" 10 |> assertError
    "overflow in bit-vector construction \
    (specified bit-vector size 8 too small to hold value -256)"
  tm.mkBitVectorOfString 8 "257" 10 |> assertError
    "overflow in bit-vector construction \
    (specified bit-vector size 8 too small to hold value 257)"
  tm.mkBitVectorOfString 8 "-a0" 16 |> assertError
    "overflow in bit-vector construction \
    (specified bit-vector size 8 too small to hold value -a0)"
  tm.mkBitVectorOfString 8 "fffff" 16 |> assertError
    "overflow in bit-vector construction \
    (specified bit-vector size 8 too small to hold value fffff)"

  tm.mkBitVectorOfString 8 "10201010" 2 |> assertError "mpz_set_str"
  tm.mkBitVectorOfString 8 "-25x" 10 |> assertError "mpz_set_str"
  tm.mkBitVectorOfString 8 "2x7" 10 |> assertError "mpz_set_str"
  tm.mkBitVectorOfString 8 "fzff" 16 |> assertError "mpz_set_str"

  assertEq (← tm.mkBitVectorOfString 8 "0101" 2) (← tm.mkBitVectorOfString 8 "00000101" 2)
  assertEq (← tm.mkBitVectorOfString 4 "-1" 2) (← tm.mkBitVectorOfString 4 "1111" 2)
  assertEq (← tm.mkBitVectorOfString 4 "-1" 16) (← tm.mkBitVectorOfString 4 "1111" 2)
  assertEq (← tm.mkBitVectorOfString 4 "-1" 10) (← tm.mkBitVectorOfString 4 "1111" 2)
  assertEq "#b01010101" (← tm.mkBitVectorOfString 8 "01010101" 2).toString
  assertEq "#b00001111" (← tm.mkBitVectorOfString 8 "F" 16).toString
  assertEq (← tm.mkBitVectorOfString 8 "-1" 10) (← tm.mkBitVectorOfString 8 "FF" 16)

test![TestApiBlackTermManager, mkFiniteFieldElem] tm => do
  let f ← tm.mkFiniteFieldSort 7
  let bv ← tm.mkBitVectorSort 4

  tm.mkFiniteFieldElem "0" f |> assertOkDiscard
  tm.mkFiniteFieldElem "1" f |> assertOkDiscard
  tm.mkFiniteFieldElem "6" f |> assertOkDiscard
  tm.mkFiniteFieldElem "8" f |> assertOkDiscard
  tm.mkFiniteFieldElem "-1" f |> assertOkDiscard

  tm.mkFiniteFieldElem "a" f |> assertError "mpz_set_str"

  tm.mkFiniteFieldElem "-1" bv |> assertError
    "invalid argument '(_ BitVec 4)' for 'sort', expected a finite field sort"

  assertEq (← tm.mkFiniteFieldElem "-1" f) (← tm.mkFiniteFieldElem "6" f)
  assertEq (← tm.mkFiniteFieldElem "1" f) (← tm.mkFiniteFieldElem "8" f)

  tm.mkFiniteFieldElem "0" f 2 |> assertOkDiscard
  tm.mkFiniteFieldElem "101" f 3 |> assertOkDiscard
  tm.mkFiniteFieldElem "-10" f 7 |> assertOkDiscard
  tm.mkFiniteFieldElem "abcde" f 16 |> assertOkDiscard

  assertEq (← tm.mkFiniteFieldElem "0" f 2) (← tm.mkFiniteFieldElem "0" f 3)
  assertEq (← tm.mkFiniteFieldElem "11" f 2) (← tm.mkFiniteFieldElem "10" f 3)
  assertEq (← tm.mkFiniteFieldElem "1010" f 2) (← tm.mkFiniteFieldElem "A" f 16)

  assertEq (← tm.mkFiniteFieldElem "-22" f 3) (← tm.mkFiniteFieldElem "10" f 6)

test![TestApiBlackTermManager, mkConstArray] tm => do
  let intSort ← tm.getIntegerSort
  let arrSort ← tm.mkArraySort intSort intSort
  let zero ← tm.mkInteger 0
  let _constArr ← tm.mkConstArray arrSort zero -- unused in original test

  tm.mkConstArray (cvc5.Sort.null ()) zero |> assertError
    "invalid null argument for 'sort'"
  tm.mkConstArray arrSort (Term.null ()) |> assertError
    "invalid null argument for 'val'"
  tm.mkConstArray arrSort (← tm.mkBitVector 1 1) |> assertError
    "value does not match element sort"

  let zero2 ← tm.mkInteger 0
  let arrSort2 ← tm.mkArraySort (← tm.getIntegerSort) (← tm.getIntegerSort)
  tm.mkConstArray arrSort2 zero |> assertOkDiscard
  tm.mkConstArray arrSort zero2 |> assertOkDiscard
  let tm' ← TermManager.new
  let int' ← tm'.getIntegerSort
  tm'.mkConstArray arrSort (← tm'.mkInteger 0) |> assertError
    "Given sort is not associated with this term manager"
  tm'.mkConstArray (← tm'.mkArraySort int' int') zero |> assertError
    "Given term is not associated with this term manager"

test![TestApiBlackTermManager, mkVar] tm => do
  let boolSort ← tm.getBooleanSort
  let intSort ← tm.getIntegerSort
  let funSort ← tm.mkFunctionSort #[intSort] boolSort
  tm.mkVar boolSort |> assertOkDiscard
  tm.mkVar funSort |> assertOkDiscard
  tm.mkVar boolSort "b" |> assertOkDiscard
  tm.mkVar funSort "" |> assertOkDiscard
  tm.mkVar (Sort.null ()) |> assertError "invalid null argument for 'sort'"
  tm.mkVar (Sort.null ()) "a" |> assertError "invalid null argument for 'sort'"
  tm.mkVar boolSort "x" |> assertOkDiscard
  let tm' ← TermManager.new
  tm'.mkVar boolSort "c" |> assertError "Given sort is not associated with this term manager"

test![TestApiBlackTermManager, mkBoolean] tm => do
  tm.mkBoolean true |> assertOkDiscard
  tm.mkBoolean false |> assertOkDiscard

test![TestApiBlackTermManager, mkRoundingMode] tm => do
  assertEq "roundNearestTiesToEven"
    (← tm.mkRoundingMode RoundingMode.ROUND_NEAREST_TIES_TO_EVEN).toString
  assertEq "roundTowardPositive"
    (← tm.mkRoundingMode RoundingMode.ROUND_TOWARD_POSITIVE).toString
  assertEq "roundTowardNegative"
    (← tm.mkRoundingMode RoundingMode.ROUND_TOWARD_NEGATIVE).toString
  assertEq "roundTowardZero"
    (← tm.mkRoundingMode RoundingMode.ROUND_TOWARD_ZERO).toString
  assertEq "roundNearestTiesToAway"
    (← tm.mkRoundingMode RoundingMode.ROUND_NEAREST_TIES_TO_AWAY).toString

test![TestApiBlackTermManager, mkRoundingMode] tm => do
  let t1 ← tm.mkBitVector 8
  let t2 ← tm.mkBitVector 4
  tm.mkFloatingPoint 3 5 t1 |> assertOkDiscard
  tm.mkFloatingPoint 0 5 (Term.null ()) |> assertError "invalid null argument for 'val'"
  tm.mkFloatingPoint 0 5 t1 |> assertError
    "invalid argument '0' for 'exp', expected exponent size > 1"
  tm.mkFloatingPoint 1 5 t1 |> assertError
    "invalid argument '1' for 'exp', expected exponent size > 1"
  tm.mkFloatingPoint 3 0 t1 |> assertError
    "invalid argument '0' for 'sig', expected significand size > 1"
  tm.mkFloatingPoint 3 1 t1 |> assertError
    "invalid argument '1' for 'sig', expected significand size > 1"
  tm.mkFloatingPoint 3 3 t2 |> assertError
    "invalid argument '#b0000' for 'val', expected a bit-vector value with bit-width '6'"

  assertEq
    (← tm.mkFloatingPointOfComponents
      (← tm.mkBitVector 1) (← tm.mkBitVector 5) (← tm.mkBitVector 10))
    (← tm.mkFloatingPoint 5 11 (← tm.mkBitVector 16))
  tm.mkFloatingPointOfComponents (Term.null ()) (← tm.mkBitVector 5) (← tm.mkBitVector 10)
  |> assertError "invalid null argument for 'sign'"
  tm.mkFloatingPointOfComponents (← tm.mkBitVector 1) (Term.null ()) (← tm.mkBitVector 10)
  |> assertError "invalid null argument for 'exp'"
  tm.mkFloatingPointOfComponents (← tm.mkBitVector 1) (← tm.mkBitVector 5) (Term.null ())
  |> assertError "invalid null argument for 'sig'"
  tm.mkFloatingPointOfComponents
    (← tm.mkConst (← tm.mkBitVectorSort 1)) (← tm.mkBitVector 5) (← tm.mkBitVector 10)
  |> assertError "invalid argument '||' for 'sign', expected bit-vector value"
  tm.mkFloatingPointOfComponents
    (← tm.mkBitVector 1) (← tm.mkConst (← tm.mkBitVectorSort 5)) (← tm.mkBitVector 10)
  |> assertError "invalid argument '||' for 'exp', expected bit-vector value"
  tm.mkFloatingPointOfComponents
    (← tm.mkBitVector 1) (← tm.mkBitVector 5) (← tm.mkConst (← tm.mkBitVectorSort 5))
  |> assertError "invalid argument '||' for 'sig', expected bit-vector value"
  tm.mkFloatingPointOfComponents
    (← tm.mkBitVector 2) (← tm.mkBitVector 5) (← tm.mkBitVector 10)
  |> assertError "invalid argument '#b00' for 'sign', expected a bit-vector value of size 1"

  let tm' ← TermManager.new
  tm'.mkFloatingPoint 3 5 t1 |> assertError
    "Given term is not associated with this term manager"
  tm'.mkFloatingPointOfComponents (← tm.mkBitVector 1) (← tm'.mkBitVector 5) (← tm'.mkBitVector 10)
  |> assertError "Given term is not associated with this term manager"
  tm'.mkFloatingPointOfComponents (← tm'.mkBitVector 1) (← tm.mkBitVector 5) (← tm'.mkBitVector 10)
  |> assertError "Given term is not associated with this term manager"
  tm'.mkFloatingPointOfComponents (← tm'.mkBitVector 1) (← tm'.mkBitVector 5) (← tm.mkBitVector 10)
  |> assertError "Given term is not associated with this term manager"

test![TestApiBlackTermManager, mkCardinalityConstraint] tm => do
  let su ← tm.mkUninterpretedSort "u"
  let si ← tm.getIntegerSort
  tm.mkCardinalityConstraint su 3 |> assertOkDiscard
  tm.mkCardinalityConstraint si 3 |> assertError
    "invalid argument 'Int' for 'sort', expected an uninterpreted sort"
  tm.mkCardinalityConstraint su 0 |> assertError
    "invalid argument '0' for 'upperBound', expected a value > 0"
  tm.mkCardinalityConstraint su 3 |> assertOkDiscard
  let tm' ← TermManager.new
  tm'.mkCardinalityConstraint su 3 |> assertError
    "Given sort is not associated with this term manager"

test![TestApiBlackTermManager, mkEmptyBag] tm => do
  let s ← tm.mkSetSort (← tm.getBooleanSort)
  tm.mkEmptySet (Sort.null ()) |> assertError
    "invalid null argument for 'sort'"
  tm.mkEmptySet s |> assertOkDiscard
  tm.mkEmptySet (← tm.getBooleanSort) |> assertError
    "invalid argument 'Bool' for 'sort', expected null sort or set sort"
  tm.mkEmptySet s |> assertOkDiscard
  let tm' ← TermManager.new
  tm'.mkEmptySet s |> assertError
    "Given sort is not associated with this term manager"

test![TestApiBlackTermManager, mkEmptyBag] tm => do
  let s ← tm.mkBagSort (← tm.getBooleanSort)
  tm.mkEmptyBag (Sort.null ()) |> assertError
    "invalid null argument for 'sort'"
  tm.mkEmptyBag s |> assertOkDiscard
  tm.mkEmptyBag (← tm.getBooleanSort) |> assertError
    "invalid argument 'Bool' for 'sort', expected null sort or bag sort"
  tm.mkEmptyBag s |> assertOkDiscard
  let tm' ← TermManager.new
  tm'.mkEmptyBag s |> assertError
    "Given sort is not associated with this term manager"

test![TestApiBlackTermManager, mkEmptySequence] tm => do
  let s ← tm.mkSequenceSort (← tm.getBooleanSort)
  tm.mkEmptySequence s |> assertOkDiscard
  tm.mkEmptySequence (← tm.getBooleanSort) |> assertOkDiscard
  tm.mkEmptySequence s |> assertOkDiscard
  let tm' ← TermManager.new
  tm'.mkEmptySequence s |> assertError
    "Given sort is not associated with this term manager"

test![TestApiBlackTermManager, mkFalse] tm => do
  tm.mkFalse |> assertOkDiscard
  tm.mkFalse |> assertOkDiscard

test![TestApiBlackTermManager, mkFloatingPointNaN] tm => do
  tm.mkFloatingPointNaN 3 5 |> assertOkDiscard

test![TestApiBlackTermManager, mkFloatingPointNegZero] tm => do
  tm.mkFloatingPointNegZero 3 5 |> assertOkDiscard

test![TestApiBlackTermManager, mkFloatingPointNegInf] tm => do
  tm.mkFloatingPointNegInf 3 5 |> assertOkDiscard

test![TestApiBlackTermManager, mkFloatingPointPosInf] tm => do
  tm.mkFloatingPointPosInf 3 5 |> assertOkDiscard

test![TestApiBlackTermManager, mkFloatingPointPosZero] tm => do
  tm.mkFloatingPointPosZero 3 5 |> assertOkDiscard
