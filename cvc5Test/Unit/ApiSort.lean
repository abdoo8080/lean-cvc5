import cvc5Test.Init

/-! # Black box testing of the guards of the Lean API functions

- <https://github.com/cvc5/cvc5/blob/main/test/unit/api/cpp/api_sort_black.cpp>
-/

namespace cvc5.Test

test![TestApiBlackSort, hash] tm => do
  assertEq tm.getIntegerSort.hash tm.getIntegerSort.hash
  assertNe tm.getIntegerSort.hash tm.getStringSort.hash

test![TestApiBlackSort, operatorsComparison] tm => do
  assertFalse (tm.getIntegerSort == Sort.null ())
  assertTrue (tm.getIntegerSort != Sort.null ())
  assertFalse (tm.getIntegerSort < Sort.null ())
  assertFalse (tm.getIntegerSort ≤ Sort.null ())
  assertTrue (tm.getIntegerSort > Sort.null ())
  assertTrue (tm.getIntegerSort ≥ Sort.null ())

test![TestApiBlackSort, getKind] tm => do
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
  let abs ← tm.mkAbstractSort SortKind.BITVECTOR_SORT
  assertEq abs.getKind SortKind.ABSTRACT_SORT

test![TestApiBlackSort, hasGetSymbol] tm => do
  let n := cvc5.Sort.null ()
  let b := tm.getBooleanSort
  let s0 := tm.mkParamSort "s0"
  let s1 := tm.mkParamSort "|s1\\|"

  assertError
    "invalid call to 'bool cvc5::Sort::hasSymbol() const', \
    expected non-null object"
    n.hasSymbol
  assertFalse (← assertOk b.hasSymbol)
  assertTrue (← assertOk s0.hasSymbol)
  assertTrue (← assertOk s1.hasSymbol)

  assertError
    "invalid call to 'std::string cvc5::Sort::getSymbol() const', \
    expected non-null object"
    n.getSymbol
  assertError
    "invalid call to 'std::string cvc5::Sort::getSymbol() const', \
    expected the sort to have a symbol."
    b.getSymbol
  assertFalse (← assertOk b.hasSymbol)
  assertEq (← assertOk s0.getSymbol) "s0"
  assertEq (← assertOk s1.getSymbol) "|s1\\|"

test![TestApiBlackSort, isNull] tm => do
  let n := cvc5.Sort.null ()
  assertTrue n.isNull
  assertFalse tm.getBooleanSort.isNull

test![TestApiBlackSort, isBoolean] tm => do
  assertTrue tm.getBooleanSort.isBoolean
  let n := cvc5.Sort.null ()
  assertFalse n.isBoolean

test![TestApiBlackSort, isInteger] tm => do
  assertTrue tm.getIntegerSort.isInteger
  assertFalse tm.getRealSort.isInteger
  let n := cvc5.Sort.null ()
  assertFalse n.isInteger

test![TestApiBlackSort, isReal] tm => do
  assertTrue tm.getRealSort.isReal
  assertFalse tm.getIntegerSort.isReal
  let n := cvc5.Sort.null ()
  assertFalse n.isReal

test![TestApiBlackSort, isString] tm => do
  assertTrue tm.getStringSort.isString
  let n := cvc5.Sort.null ()
  assertFalse n.isString

test![TestApiBlackSort, isRegExp] tm => do
  assertTrue tm.getRegExpSort.isRegExp
  let n := cvc5.Sort.null ()
  assertFalse n.isRegExp

test![TestApiBlackSort, isRoundingMode] tm => do
  assertTrue tm.getRoundingModeSort.isRoundingMode
  let n := cvc5.Sort.null ()
  assertFalse n.isRoundingMode

test![TestApiBlackSort, isBitVector] tm => do
  assertTrue (← tm.mkBitVectorSort 8).isBitVector
  let n := cvc5.Sort.null ()
  assertFalse n.isBitVector

test![TestApiBlackSort, isFiniteField] tm => do
  assertTrue (← tm.mkFiniteFieldSort 7).isFiniteField
  let n := cvc5.Sort.null ()
  assertFalse n.isFiniteField

test![TestApiBlackSort, isFloatingPoint] tm => do
  assertTrue (← tm.mkFloatingPointSort 8 24).isFloatingPoint
  let n := cvc5.Sort.null ()
  assertFalse n.isFloatingPoint

-- test![TestApiBlackSort, isDatatype] tm => do
--   let dtSort ← tm.createDatatypeSort
--   assertTrue dtSort.isDatatype
--   let n := cvc5.Sort.null ()
--   assertFalse n.isDatatype

-- test![TestApiBlackSort, isDatatypeConstructor] tm => do
--   let dtSort ← tm.createDatatypeSort
--   let dt := dtSort.getDatatype
--   let consSort := dt[0].getTerm.getSort
--   -- assertError "failure" dt[3] -- not possible in lean
--   assertTrue consSort.isDatatypeConstructor
--   let n := cvc5.Sort.null ()
--   assertFalse n.isDatatypeConstructor

-- test![TestApiBlackSort, isDatatypeSelector] tm => do
--   let dtSort ← tm.createDatatypeSort
--   let dt := dtSort.getDatatype
--   let selSort := dt[0][1].getTerm.getSort
--   -- assertError "failure" dt[0][2] -- not possible in lean
--   assertTrue selSort.isDatatypeSelector
--   let n := cvc5.Sort.null ()
--   assertFalse n.isDatatypeSelector

-- test![TestApiBlackSort, isDatatypeTester] tm => do
--   let dtSort ← tm.createDatatypeSort
--   let dt := dtSort.getDatatype
--   let testerSort := dt[0].getTesterTerm.getSort
--   -- assertError "failure" dt[3] -- not possible in lean
--   assertTrue testerSort.isDatatypeTester
--   let n := cvc5.Sort.null ()
--   assertFalse n.isDatatypeTester

-- test![TestApiBlackSort, isDatatypeUpdater] tm => do
--   let dtSort ← tm.createDatatypeSort
--   let dt := dtSort.getDatatype
--   let updaterSort := dt[0].getUpdaterTerm.getSort
--   -- assertError "failure" dt[3] -- not possible in lean
--   assertTrue updaterSort.isDatatypeUpdater
--   let n := cvc5.Sort.null ()
--   assertFalse n.isDatatypeUpdater

test![TestApiBlackSort, isFunction] tm => do
  assertTrue (← tm.mkFunctionSort #[tm.getBooleanSort] tm.getIntegerSort).isFunction
  let n := cvc5.Sort.null ()
  assertFalse n.isFunction

test![TestApiBlackSort, isPredicate] tm => do
  assertTrue (← tm.mkPredicateSort #[tm.getRealSort]).isPredicate
  let n := cvc5.Sort.null ()
  assertFalse n.isPredicate

test![TestApiBlackSort, isTuple] tm => do
  assertTrue (← tm.mkTupleSort #[tm.getRealSort]).isTuple
  let n := cvc5.Sort.null ()
  assertFalse n.isTuple

test![TestApiBlackSort, isNullable] tm => do
  assertTrue (← tm.mkNullableSort tm.getRealSort).isNullable
  let n := cvc5.Sort.null ()
  assertFalse n.isNullable

-- test![TestApiBlackSort, isRecord] tm => do
--   assertEq (← tm.mkRecordSort #[("asdf", tm.getRealSort)]).isRecord true
--   let n := cvc5.Sort.null ()
--   assertFalse n.isRecord

test![TestApiBlackSort, isArray] tm => do
  assertTrue (← tm.mkArraySort tm.getRealSort tm.getIntegerSort).isArray
  let n := cvc5.Sort.null ()
  assertFalse n.isArray

test![TestApiBlackSort, isSet] tm => do
  assertTrue (← tm.mkSetSort tm.getRealSort).isSet
  let n := cvc5.Sort.null ()
  assertFalse n.isSet

test![TestApiBlackSort, isBag] tm => do
  assertTrue (← tm.mkBagSort tm.getRealSort).isBag
  let n := cvc5.Sort.null ()
  assertFalse n.isBag

test![TestApiBlackSort, isSequence] tm => do
  assertTrue (← tm.mkSequenceSort tm.getRealSort).isSequence
  let n := cvc5.Sort.null ()
  assertFalse n.isSequence

test![TestApiBlackSort, isAbstract] tm => do
  assertTrue (← tm.mkAbstractSort SortKind.BITVECTOR_SORT).isAbstract
  assertFalse (← tm.mkAbstractSort SortKind.ARRAY_SORT).isAbstract
  assertTrue (← tm.mkAbstractSort SortKind.ABSTRACT_SORT).isAbstract
  let n := cvc5.Sort.null ()
  assertFalse n.isAbstract

test![TestApiBlackSort, isUninterpreted] tm => do
  assertTrue (tm.mkUninterpretedSort "asdf").isUninterpretedSort
  let n := cvc5.Sort.null ()
  assertFalse n.isUninterpretedSort

test![TestApiBlackSort, isUninterpretedSortConstructor] tm => do
  let scSort ← tm.mkUninterpretedSortConstructorSort 1 "asdf"
  assertTrue scSort.isUninterpretedSortConstructor
  let scSort2 ← tm.mkUninterpretedSortConstructorSort 2 "asdf"
  assertTrue scSort2.isUninterpretedSortConstructor

-- test![TestApiBlackSort, getDatatype] tm => do
--   let dTypeSort ← createDatatypeSort
--   assertOkDiscard dTypeSort.getDatatype
--   -- create bv sort, check should fail
--   let bvSort ← tm.mkBitVectorSort 32
--   assertError "failure" bvSort.getDatatype

-- test![TestApiBlackSort, datatypeSorts] tm => do
--   let intSort := tm.getIntegerSort
--   let dTypeSort ← createDatatypeSort
--   let dt ← dTypeSort.getDatatype
--   assertFalse dTypeSort.isDatatypeConstructor
--   assertError "failure" dTypeSort.getDatatypeConstructorCodomainSort
--   assertError "failure" dTypeSort.getDatatypeConstructorDomainSorts
--   assertError "failure" dTypeSort.getDatatypeConstructorArity

--   -- get constructor
--   let dCons := dt[0]
--   let consTerm := dCons.getTerm
--   let consort := consTerm.getSort
--   assertTrue consSort.isDatatypeConstructor
--   assertFalse consSort.isDatatypeTester
--   assertFalse consSort.isDatatypeSelector
--   assertEq (← consSort.getDatatypeConstructorArity) 2
--   let consDomSorts ← consSort.getDatatypeConstructorDomainSorts
--   assertEq consDomSorts[0] intSort
--   assertEq consDomSorts[1] dTypeSort
--   assertEq consSort.getDatatypeConstructorCodomainSort dTypeSort

--   -- get tester
--   let testerTerm ← dCons.getTesterTerm
--   assertTrue testerTerm.getSort.isDatatypeTester
--   assertEq (← testerTerm.getSort.getDatatypeTesterDomainSort) dTypeSort
--   let booleanSort := tm.getBooleanSort
--   assertEq (← testerTerm.getSort.getDatatypeTesterCodomainSort) booleanSort
--   assertError "failure" booleanSort.getDatatypeTesterDomainSort
--   assertError "failure" booleanSort.getDatatypeTesterCodomainSort

--   -- get selector
--   let dSelTail := dCons[1]
--   let tailTerm ← dSelTail.getTerm
--   assertTrue tailTerm.getSort.isDatatypeSelector
--   assertEq tailTerm.getSort.getDatatypeSelectorDomainSort dTypeSort
--   assertEq tailTerm.getSort.getDatatypeSelectorCodomainSort dTypeSort
--   assertError "failure" booleanSort.getDatatypeSelectorDomainSort
--   assertError "failure" booleanSort.getDatatypeSelectorCodomainSort

-- test![TestApiBlackSort, instantiate] tm => do
--   -- instantiate parametric datatype, check should not fail
--   let paramDTypeSort ← createParamDatatypeSort
--   assertOkDiscard (paramDTypeSort.instantiate #[tm.getIntegerSort])
--   -- instantiate non-parametric datatype sort, check should fail
--   let mut dTypeSpec ← tm.mkDatatypeDecl "list"
--   let mut cons ← tm.mkDatatypeConstructorDecl "cons"
--   cons := cons.addSelector "head" tm.getIntegerSort
--   dTypeSpec := dTypeSpec.addConstructor cons
--   let nil ← tm.mkDatatypeConstructorDecl "nil"
--   dTypeSpec := dTypeSpec.addConstructor nil
--   let dTypeSort ← tm.mkDatatypeSort dTypeSpec
--   assertError "failure" (dTypeSort.instantiate #[tm.getIntegerSort])
--   -- instantiate uninterpreted sort constructor
--   let sortConsSort ← tm.mkUninterpretedSortConstructorSort 1 "s"
--   assertOkDiscard (sortConsSort.instantiate #[tm.getIntegerSort])

test![TestApiBlackSort, instantiate] tm => do
  -- let paramDTypeSort ← createParamDatatypeSort
  -- assertFalse paramDTypeSort.isInstantiated
  -- let instParamDTypeSort ← paramDTypeSort.instantiate #[tm.getIntegerSort]
  -- assertTrue instParamDTypeSort.isInstantiated

  let sortConsSort ← tm.mkUninterpretedSortConstructorSort 1 "s"
  assertFalse sortConsSort.isInstantiated
  let instSortConsSort ← sortConsSort.instantiate #[tm.getIntegerSort]
  assertTrue instSortConsSort.isInstantiated

  assertFalse tm.getIntegerSort.isInstantiated
  assertFalse (← tm.mkBitVectorSort 32 ).isInstantiated

-- test![TestApiBlackSort, getInstantiatedParameters] tm => do
--   let intSort := tm.getIntegerSort
--   let realSort := tm.getRealSort
--   let boolSort := tm.getBooleanSort
--   let bvSort ← tm.mkBitVectorSort 8

--   -- parametric datatype instantiation
--   let p1 := tm.mkParamSort "p1"
--   let p2 := tm.mkParamSort "p2"
--   let mut pSpec ← tm.mkDatatypeDecl "pdtype" #[p1, p2]
--   let mut pCons1 ← tm.mkDatatypeConstructorDecl "cons1"
--   let mut pCons2 ← tm.mkDatatypeConstructorDecl "cons2"
--   let pNil ← tm.mkDatatypeConstructorDecl "nil"
--   pCons1 := pCons1.addSelector "sel" p1
--   pCons2 := pCons2.addSelector "sel" p2
--   pSpec := pSpec.addConstructor pCons1
--   pSpec := pSpec.addConstructor pCons2
--   pSpec := pSpec.addConstructor pNil
--   let paramDTypeSort ← tm.mkDatatypeSort pSpec

--   assertError "failure" paramDTypeSort.getInstantiatedParameters

--   let instParamDTypeSort ← paramDTypeSort.instantiate #[realSort, boolSort]

--   let instSorts ← instParamDTypeSort.getInstantiatedParameters
--   assertEq instSorts[0] realSort
--   assertEq instSorts[1] boolSort

--   -- uninterpreted sort constructor sort instantiation
--   let sortConsSort ← tm.mkUninterpretedSortConstructorSort 4 "s"
--   assertError "failure" sortConsSort.getInstantiatedParameters

--   let instSortConsSort ← sortConsSort.instantiate #[boolSort, intSort, bvSort, realSort]

--   let instSorts ← instSortConsSort.getInstantiatedParameters
--   assertEq instSorts[0] boolSort
--   assertEq instSorts[1] intSort
--   assertEq instSorts[2] bvSort
--   assertEq instSorts[3] realSort

--   assertError "failure" intSort.getInstantiatedParameters
--   assertError "failure" bvSort.getInstantiatedParameters

test![TestApiBlackSort, getUninterpretedSortConstructor] tm => do
  let intSort := tm.getIntegerSort
  let realSort := tm.getRealSort
  let boolSort := tm.getBooleanSort
  let bvSort ← tm.mkBitVectorSort 8
  let sortConsSort ← tm.mkUninterpretedSortConstructorSort 4 "s"
  sortConsSort.getUninterpretedSortConstructor
  |> assertError "expected instantiated uninterpreted sort."
  let instSortConsSort ← sortConsSort.instantiate #[boolSort, intSort, bvSort, realSort]
  assertEq sortConsSort (← instSortConsSort.getUninterpretedSortConstructor)

test![TestApiBlackSort, getFunctionArity] tm => do
  let funSort ← tm.mkFunctionSort #[tm.mkUninterpretedSort "u"] tm.getIntegerSort
  assertEq (← funSort.getFunctionArity) 1
  let bvSort ← tm.mkBitVectorSort 32
  assertError "not a function sort: (_ BitVec 32)" bvSort.getFunctionArity

test![TestApiBlackSort, getFunctionDomainSorts] tm => do
  let funSort ← tm.mkFunctionSort #[tm.mkUninterpretedSort "u"] tm.getIntegerSort
  assertOkDiscard funSort.getFunctionDomainSorts
  let bvSort ← tm.mkBitVectorSort 32
  assertError "not a function sort: (_ BitVec 32)" bvSort.getFunctionDomainSorts

test![TestApiBlackSort, getFunctionCodomainSort] tm => do
  let funSort ← tm.mkFunctionSort #[tm.mkUninterpretedSort "u"] tm.getIntegerSort
  assertOkDiscard funSort.getFunctionCodomainSort
  let bvSort ← tm.mkBitVectorSort 32
  assertError "not a function sort(_ BitVec 32)" bvSort.getFunctionCodomainSort

test![TestApiBlackSort, getArrayIndexSort] tm => do
  let elementSort ← tm.mkBitVectorSort 32
  let indexSort ← tm.mkBitVectorSort 32
  let arraySort ← tm.mkArraySort indexSort elementSort
  assertOkDiscard arraySort.getArrayIndexSort
  assertError "not an array sort." indexSort.getArrayIndexSort

test![TestApiBlackSort, getArrayElementSort] tm => do
  let elementSort ← tm.mkBitVectorSort 32
  let indexSort ← tm.mkBitVectorSort 32
  let arraySort ← tm.mkArraySort indexSort elementSort
  assertOkDiscard arraySort.getArrayElementSort
  assertError "not an array sort." indexSort.getArrayElementSort

test![TestApiBlackSort, getSetElementSort] tm => do
  let setSort ← tm.mkSetSort tm.getIntegerSort
  let elementSort ← assertOk setSort.getSetElementSort
  assertEq elementSort tm.getIntegerSort
  let bvSort ← tm.mkBitVectorSort 32
  assertError "not a set sort." bvSort.getSetElementSort

test![TestApiBlackSort, getBagElementSort] tm => do
  let bagSort ← tm.mkBagSort tm.getIntegerSort
  let elementSort ← assertOk bagSort.getBagElementSort
  assertEq elementSort tm.getIntegerSort
  let bvSort ← tm.mkBitVectorSort 32
  assertError "not a bag sort." bvSort.getBagElementSort

test![TestApiBlackSort, getSequenceElementSort] tm => do
  let seqSort ← tm.mkSequenceSort tm.getIntegerSort
  let elementSort ← assertOk seqSort.getSequenceElementSort
  assertEq elementSort tm.getIntegerSort
  let bvSort ← tm.mkBitVectorSort 32
  assertError "not a sequence sort." bvSort.getSequenceElementSort

test![TestApiBlackSort, getAbstractedKind] tm => do
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

test![TestApiBlackSort, getSymbol] tm => do
  let uSort := tm.mkUninterpretedSort "u"
  assertEq (← uSort.getSymbol) "u"
  let bvSort ← tm.mkBitVectorSort 32
  assertError
    "invalid call to 'std::string cvc5::Sort::getSymbol() const', \
    expected the sort to have a symbol."
    bvSort.getSymbol

test![TestApiBlackSort, getUninterpretedSortConstructorName] tm => do
  let sSort ← tm.mkUninterpretedSortConstructorSort 2 "s"
  assertEq (← sSort.getSymbol) "s"
  let bvSort ← tm.mkBitVectorSort 32
  assertError
    "invalid call to 'std::string cvc5::Sort::getSymbol() const', \
    expected the sort to have a symbol."
    bvSort.getSymbol

test![TestApiBlackSort, getUninterpretedSortConstructorArity] tm => do
  let sSort ← tm.mkUninterpretedSortConstructorSort 2 "s"
  assertEq (← sSort.getUninterpretedSortConstructorArity) 2
  let bvSort ← tm.mkBitVectorSort 32
  assertError
    "not a sort constructor sort."
    bvSort.getUninterpretedSortConstructorArity

test![TestApiBlackSort, getBitVectorSize] tm => do
  let bvSort ← tm.mkBitVectorSort 32
  assertEq (← bvSort.getBitVectorSize) 32
  let setSort ← tm.mkSetSort tm.getIntegerSort
  assertError "not a bit-vector sort." setSort.getBitVectorSize

test![TestApiBlackSort, getFiniteFieldSize] tm => do
  let ffSort ← tm.mkFiniteFieldSort 31
  assertOkDiscard ffSort.getFiniteFieldSize
  assertEq (← ffSort.getFiniteFieldSize) 31
  (cvc5.Sort.null ()).getFiniteFieldSize |> assertError
    "invalid call to 'std::string cvc5::Sort::getFiniteFieldSize() const', \
    expected non-null object"

test![TestApiBlackSort, getFloatingPointExponentSize] tm => do
  let fpSort ← tm.mkFloatingPointSort 4 8
  assertEq (← fpSort.getFloatingPointExponentSize) 4
  let setSort ← tm.mkSetSort tm.getIntegerSort
  assertError "not a floating-point sort." setSort.getFloatingPointExponentSize

test![TestApiBlackSort, getFloatingPointSignificandSize] tm => do
  let fpSort ← tm.mkFloatingPointSort 4 8
  assertEq (← fpSort.getFloatingPointSignificandSize) 8
  let setSort ← tm.mkSetSort tm.getIntegerSort
  assertError "not a floating-point sort." setSort.getFloatingPointSignificandSize

-- test![TestApiBlackSort, getDatatypeArity] tm => do
--   -- create datatype sort, check should not fail
--   let mut dTypeSpec ← tm.mkDatatypeDecl "list"
--   let mut cons ← tm.mkDatatypeConstructorDecl "cons"
--   cons := addSelector "head" tm.getIntegerSort
--   dTypeSpec := dTypeSpec.addConstructor cons
--   let nil ← tm.mkDatatypeConstructorDecl "nil"
--   dTypeSpec := dTypeSpec.addConstructor nil
--   let dTypeSort ← tm.mkDatatypeSort dTypeSpec
--   assertOkDiscard dTypeSort.getDatatypeArity
--   -- create bv sort, check should fail
--   let bvSort ← tm.mkBitVectorSort 32
--   assertError "failure" bvSort.getDatatypeArity

test![TestApiBlackSort, getTupleLength] tm => do
  let tupleSort ← tm.mkTupleSort #[tm.getIntegerSort, tm.getIntegerSort]
  assertEq (← tupleSort.getTupleLength) 2
  let bvSort ← tm.mkBitVectorSort 32
  assertError "not a tuple sort." bvSort.getTupleLength

test![TestApiBlackSort, getTupleSorts] tm => do
  let tupleSort ← tm.mkTupleSort #[tm.getIntegerSort, tm.getIntegerSort]
  assertOkDiscard tupleSort.getTupleSorts
  let bvSort ← tm.mkBitVectorSort 32
  assertError "not a tuple sort." bvSort.getTupleSorts

test![TestApiBlackSort, getNullableElementSort] tm => do
  let nullableSort ← tm.mkNullableSort tm.getIntegerSort
  assertOkDiscard nullableSort.getNullableElementSort
  let elementSort ← nullableSort.getNullableElementSort
  assertEq elementSort tm.getIntegerSort
  let bvSort ← tm.mkBitVectorSort 32
  assertError "not a nullable sort." bvSort.getNullableElementSort

test![TestApiBlackSort, sortCompare] tm => do
  let boolSort := tm.getBooleanSort
  let intSort := tm.getIntegerSort
  let bvSort ← tm.mkBitVectorSort 32
  let bvSort2 ← tm.mkBitVectorSort 32
  assertTrue (bvSort ≥ bvSort2)
  assertTrue (bvSort ≤ bvSort2)
  assertTrue ((intSort > boolSort) ≠ (intSort < boolSort))
  assertTrue ((intSort > bvSort ∨ intSort == bvSort) = (intSort ≥ bvSort))

test![TestApiBlackSort, sortScopedToString] tm => do
  let name := "uninterp-sort"
  let bvSort8 ← tm.mkBitVectorSort 8
  let uSort := tm.mkUninterpretedSort name
  -- repetition present in the original test
  assertEq bvSort8.toString "(_ BitVec 8)"
  assertEq uSort.toString name
  assertEq bvSort8.toString "(_ BitVec 8)"
  assertEq uSort.toString name

test![TestApiBlackSort, toString] tm => do
  -- useless test here, as `toString` is not expected to fail at all
  assertOkDiscard (return (Sort.null ()).toString)

test![TestApiBlackSort, substitute] tm => do
  let sortVar0 := tm.mkParamSort "T0"
  let sortVar1 := tm.mkParamSort "T1"
  let intSort := tm.getIntegerSort
  let realSort := tm.getRealSort
  let arraySort0 ← tm.mkArraySort sortVar0 sortVar0
  let arraySort1 ← tm.mkArraySort sortVar0 sortVar1
  -- now create instantiations of the defined sorts
  assertOkDiscard
    (arraySort0.substitute #[sortVar0] #[intSort])
  assertOkDiscard
    (arraySort1.substitute #[sortVar0, sortVar1] #[intSort, realSort])
