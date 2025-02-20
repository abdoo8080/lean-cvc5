import cvc5Test.Init

/-! # Black box testing of the guards of the Lean API functions

- <https://github.com/cvc5/cvc5/blob/main/test/unit/api/cpp/api_sort_black.cpp>
-/

namespace cvc5.Test

test! tm => do
  let s1 := tm.getIntegerSort
  let s1' := tm.getIntegerSort
  let s2 := tm.getStringSort
  assertEq s1 s1'
  assertNe s1 s2

test! tm => do
  let s1 := tm.getIntegerSort
  let s2 := cvc5.Sort.null ()
  assertEq (s1 == s2) false
  assertEq (s1 != s2) true

test! tm => do
  let b := tm.getBooleanSort
  assertEq b.getKind SortKind.BOOLEAN_SORT
  -- let dtSort ← tm.createDatatypeSort -- should be (some variant of) `mkDatatypeSort`?
  -- assertEq dtSort.getKind SortKnd.DATATYPE_SORT
  let r := tm.getRealSort
  let i := tm.getIntegerSort
  let arr ← tm.mkArraySort r i
  assertEq arr.getKind SortKind.ARRAY_SORT
  let fp ← tm.mkFloatingPointSort 8 24
  assertEq fp.getKind SortKind.FLOATINGPOINT_SORT
  let bv ← tm.mkBitVectorSort 8
  assertEq bv.getKind SortKind.BITVECTOR_SORT
  -- let abs ← tm.mkAbstractSort SortKind.BITVECTOR_SORT
  -- assertEq abs.getKind SortKind.ABSTRACT_SORT

test! tm => do
  let n := cvc5.Sort.null ()
  let b := tm.getBooleanSort
  let s0 := tm.mkParamSort "s0"
  let s1 := tm.mkParamSort "|s1\\|"

  assertError
    "invalid call to 'bool cvc5::Sort::hasSymbol() const', \
    expected non-null object"
    n.hasSymbol
  assertEq (← assertOk b.hasSymbol) false
  assertEq (← assertOk s0.hasSymbol) true
  assertEq (← assertOk s1.hasSymbol) true

  assertError
    "invalid call to 'std::string cvc5::Sort::getSymbol() const', \
    expected non-null object"
    n.getSymbol
  assertError
    "invalid call to 'std::string cvc5::Sort::getSymbol() const', \
    expected the sort to have a symbol."
    b.getSymbol
  assertEq (← assertOk b.hasSymbol) false
  assertEq (← assertOk s0.getSymbol) "s0"
  assertEq (← assertOk s1.getSymbol) "|s1\\|"

test! tm => do
  let n := cvc5.Sort.null ()
  assertEq n.isNull true
  assertEq tm.getBooleanSort.isNull false

test! tm => do
  assertEq tm.getBooleanSort.isBoolean true
  let n := cvc5.Sort.null ()
  assertEq n.isBoolean false

test! tm => do
  assertEq tm.getIntegerSort.isInteger true
  assertEq tm.getRealSort.isInteger false
  let n := cvc5.Sort.null ()
  assertEq n.isInteger false

test! tm => do
  assertEq tm.getRealSort.isReal true
  assertEq tm.getIntegerSort.isReal false
  let n := cvc5.Sort.null ()
  assertEq n.isReal false

test! tm => do
  assertEq tm.getStringSort.isString true
  let n := cvc5.Sort.null ()
  assertEq n.isString false

test! tm => do
  assertEq tm.getRegExpSort.isRegExp true
  let n := cvc5.Sort.null ()
  assertEq n.isRegExp false

test! tm => do
  assertEq tm.getRoundingModeSort.isRoundingMode true
  let n := cvc5.Sort.null ()
  assertEq n.isRoundingMode false

test! tm => do
  assertEq (← tm.mkBitVectorSort 8).isBitVector true
  let n := cvc5.Sort.null ()
  assertEq n.isBitVector false

test! tm => do
  assertEq (← tm.mkFiniteFieldSort "7").isFiniteField true
  let n := cvc5.Sort.null ()
  assertEq n.isFiniteField false

test! tm => do
  assertEq (← tm.mkFloatingPointSort 8 24).isFloatingPoint true
  let n := cvc5.Sort.null ()
  assertEq n.isFloatingPoint false

-- test! tm => do
--   let dtSort ← tm.createDatatypeSort
--   assertEq dtSort.isDatatype true
--   let n := cvc5.Sort.null ()
--   assertEq n.isDatatype false

-- test! tm => do
--   let dtSort ← tm.createDatatypeSort
--   let dt := dtSort.getDatatype
--   let consSort := dt[0].getTerm.getSort
--   -- assertError "failure" dt[3] -- not possible in lean
--   assertEq consSort.isDatatypeConstructor true
--   let n := cvc5.Sort.null ()
--   assertEq n.isDatatypeConstructor false

-- test! tm => do
--   let dtSort ← tm.createDatatypeSort
--   let dt := dtSort.getDatatype
--   let testerSort := dt[0].getTesterTerm.getSort
--   -- assertError "failure" dt[3] -- not possible in lean
--   assertEq testerSort.isDatatypeTester true
--   let n := cvc5.Sort.null ()
--   assertEq n.isDatatypeTester false

-- test! tm => do
--   let dtSort ← tm.createDatatypeSort
--   let dt := dtSort.getDatatype
--   let updaterSort := dt[0].getUpdaterTerm.getSort
--   -- assertError "failure" dt[3] -- not possible in lean
--   assertEq updaterSort.isDatatypeUpdater true
--   let n := cvc5.Sort.null ()
--   assertEq n.isDatatypeUpdater false

test! tm => do
  assertEq (← tm.mkFunctionSort #[tm.getBooleanSort] tm.getIntegerSort).isFunction true
  let n := cvc5.Sort.null ()
  assertEq n.isFunction false

test! tm => do
  assertEq (← tm.mkPredicateSort #[tm.getRealSort]).isPredicate true
  let n := cvc5.Sort.null ()
  assertEq n.isPredicate false

test! tm => do
  assertEq (← tm.mkTupleSort #[tm.getRealSort]).isTuple true
  let n := cvc5.Sort.null ()
  assertEq n.isTuple false

test! tm => do
  assertEq (← tm.mkNullableSort tm.getRealSort).isNullable true
  let n := cvc5.Sort.null ()
  assertEq n.isNullable false

-- test! tm => do
--   assertEq (← tm.mkRecordSort #[("asdf", tm.getRealSort)]).isRecord true
--   let n := cvc5.Sort.null ()
--   assertEq n.isRecord false

test! tm => do
  assertEq (← tm.mkArraySort tm.getRealSort tm.getIntegerSort).isArray true
  let n := cvc5.Sort.null ()
  assertEq n.isArray false

test! tm => do
  assertEq (← tm.mkSetSort tm.getRealSort).isSet true
  let n := cvc5.Sort.null ()
  assertEq n.isSet false

test! tm => do
  assertEq (← tm.mkBagSort tm.getRealSort).isBag true
  let n := cvc5.Sort.null ()
  assertEq n.isBag false

test! tm => do
  assertEq (← tm.mkSequenceSort tm.getRealSort).isSequence true
  let n := cvc5.Sort.null ()
  assertEq n.isSequence false

test! tm => do
  assertEq (← tm.mkAbstractSort SortKind.BITVECTOR_SORT).isAbstract true
  assertEq (← tm.mkAbstractSort SortKind.ARRAY_SORT).isAbstract false
  assertEq (← tm.mkAbstractSort SortKind.ABSTRACT_SORT).isAbstract true
  let n := cvc5.Sort.null ()
  assertEq n.isAbstract false

test! tm => do
  assertEq (tm.mkUninterpretedSort "asdf").isUninterpretedSort true
  let n := cvc5.Sort.null ()
  assertEq n.isUninterpretedSort false

/-!
Datatype-related tests go here.
-/

test! tm => do
  let intSort := tm.getIntegerSort
  let realSort := tm.getRealSort
  let boolSort := tm.getBooleanSort
  let bvSort ← tm.mkBitVectorSort 8
  let sortConsSort ← tm.mkUninterpretedSortConstructorSort 4 "s"
  sortConsSort.getUninterpretedSortConstructor
  |> assertError "expected instantiated uninterpreted sort."
  let instSortConsSort ← sortConsSort.instantiate #[boolSort, intSort, bvSort, realSort]
  assertEq sortConsSort (← instSortConsSort.getUninterpretedSortConstructor)

test! tm => do
  let funSort ← tm.mkFunctionSort #[tm.mkUninterpretedSort "u"] tm.getIntegerSort
  assertEq (← funSort.getFunctionArity) 1
  let bvSort ← tm.mkBitVectorSort 32
  assertError "not a function sort: (_ BitVec 32)" bvSort.getFunctionArity

test! tm => do
  let funSort ← tm.mkFunctionSort #[tm.mkUninterpretedSort "u"] tm.getIntegerSort
  assertOkDiscard funSort.getFunctionDomainSorts
  let bvSort ← tm.mkBitVectorSort 32
  assertError "not a function sort: (_ BitVec 32)" bvSort.getFunctionDomainSorts

test! tm => do
  let funSort ← tm.mkFunctionSort #[tm.mkUninterpretedSort "u"] tm.getIntegerSort
  assertOkDiscard funSort.getFunctionCodomainSort
  let bvSort ← tm.mkBitVectorSort 32
  assertError "not a function sort(_ BitVec 32)" bvSort.getFunctionCodomainSort

test! tm => do
  let elementSort ← tm.mkBitVectorSort 32
  let indexSort ← tm.mkBitVectorSort 32
  let arraySort ← tm.mkArraySort indexSort elementSort
  assertOkDiscard arraySort.getArrayIndexSort
  assertError "not an array sort." indexSort.getArrayIndexSort

test! tm => do
  let elementSort ← tm.mkBitVectorSort 32
  let indexSort ← tm.mkBitVectorSort 32
  let arraySort ← tm.mkArraySort indexSort elementSort
  assertOkDiscard arraySort.getArrayElementSort
  assertError "not an array sort." indexSort.getArrayElementSort

test! tm => do
  let setSort ← tm.mkSetSort tm.getIntegerSort
  let elementSort ← assertOk setSort.getSetElementSort
  assertEq elementSort tm.getIntegerSort
  let bvSort ← tm.mkBitVectorSort 32
  assertError "not a set sort." bvSort.getSetElementSort

test! tm => do
  let bagSort ← tm.mkBagSort tm.getIntegerSort
  let elementSort ← assertOk bagSort.getBagElementSort
  assertEq elementSort tm.getIntegerSort
  let bvSort ← tm.mkBitVectorSort 32
  assertError "not a bag sort." bvSort.getBagElementSort

test! tm => do
  let seqSort ← tm.mkSequenceSort tm.getIntegerSort
  let elementSort ← assertOk seqSort.getSequenceElementSort
  assertEq elementSort tm.getIntegerSort
  let bvSort ← tm.mkBitVectorSort 32
  assertError "not a sequence sort." bvSort.getSequenceElementSort

test! tm => do
  assertEq
    (← (← tm.mkAbstractSort SortKind.BITVECTOR_SORT).getAbstractedKind)
    SortKind.BITVECTOR_SORT
  -- `?Array` is syntax sugar for `(Array ? ?)`, thus the constructed sort is an `Array` sort, not
  -- an abstract sort and its abstract kind cannot be extracted
  assertError "not an abstract sort." (do
    let absSort ← tm.mkAbstractSort SortKind.ARRAY_SORT
    absSort.getAbstractedKind
  )
  assertEq
    (← (← tm.mkAbstractSort SortKind.ABSTRACT_SORT).getAbstractedKind)
    SortKind.ABSTRACT_SORT

test! tm => do
  let uSort := tm.mkUninterpretedSort "u"
  assertEq (← uSort.getSymbol) "u"
  let bvSort ← tm.mkBitVectorSort 32
  assertError
    "invalid call to 'std::string cvc5::Sort::getSymbol() const', \
    expected the sort to have a symbol."
    bvSort.getSymbol

test! tm => do
  let sSort ← tm.mkUninterpretedSortConstructorSort 2 "s"
  assertEq (← sSort.getSymbol) "s"
  let bvSort ← tm.mkBitVectorSort 32
  assertError
    "invalid call to 'std::string cvc5::Sort::getSymbol() const', \
    expected the sort to have a symbol."
    bvSort.getSymbol

test! tm => do
  let sSort ← tm.mkUninterpretedSortConstructorSort 2 "s"
  assertEq (← sSort.getUninterpretedSortConstructorArity) 2
  let bvSort ← tm.mkBitVectorSort 32
  assertError
    "not a sort constructor sort."
    bvSort.getUninterpretedSortConstructorArity

test! tm => do
  let bvSort ← tm.mkBitVectorSort 32
  assertEq (← bvSort.getBitVectorSize) 32
  let setSort ← tm.mkSetSort tm.getIntegerSort
  assertError "not a bit-vector sort." setSort.getBitVectorSize

test! tm => do
  let ffSort ← tm.mkFiniteFieldSort "31"
  assertOkDiscard ffSort.getFiniteFieldSize
  assertEq (← ffSort.getFiniteFieldSize) "31"
  (cvc5.Sort.null ()).getFiniteFieldSize |> assertError
    "invalid call to 'std::string cvc5::Sort::getFiniteFieldSize() const', \
    expected non-null object"

test! tm => do
  let fpSort ← tm.mkFloatingPointSort 4 8
  assertEq (← fpSort.getFloatingPointExponentSize) 4
  let setSort ← tm.mkSetSort tm.getIntegerSort
  assertError "not a floating-point sort." setSort.getFloatingPointExponentSize

test! tm => do
  let fpSort ← tm.mkFloatingPointSort 4 8
  assertEq (← fpSort.getFloatingPointSignificandSize) 8
  let setSort ← tm.mkSetSort tm.getIntegerSort
  assertError "not a floating-point sort." setSort.getFloatingPointSignificandSize

/-
`getDatatypeArity` test goes here
-/

test! tm => do
  let tupleSort ← tm.mkTupleSort #[tm.getIntegerSort, tm.getIntegerSort]
  assertEq (← tupleSort.getTupleLength) 2
  let bvSort ← tm.mkBitVectorSort 32
  assertError "not a tuple sort." bvSort.getTupleLength

test! tm => do
  let tupleSort ← tm.mkTupleSort #[tm.getIntegerSort, tm.getIntegerSort]
  assertOkDiscard tupleSort.getTupleSorts
  let bvSort ← tm.mkBitVectorSort 32
  assertError "not a tuple sort." bvSort.getTupleSorts
