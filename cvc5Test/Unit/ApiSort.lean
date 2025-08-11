/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Adrien Champion
-/
import cvc5Test.Init

/-! # Black box testing of the guards of the Lean API functions

- <https://github.com/cvc5/cvc5/blob/main/test/unit/api/cpp/api_sort_black.cpp>
-/

namespace cvc5.Test

test![TestApiBlackSort, hash] do
  let int ← cvc5.getIntegerSort
  let str ← cvc5.getStringSort
  assertEq int.hash int.hash
  assertNe int.hash str.hash

-- -- lean API does not expose a `null` sort
-- test![TestApiBlackSort, operatorsComparison] do
--   let nullSrt ← Srt.null
--   let int ← cvc5.getIntegerSort
--   assertFalse (int == nullSrt)
--   assertTrue (int != nullSrt)
--   assertFalse (int < nullSrt)
--   assertFalse (int ≤ nullSrt)
--   assertTrue (int > nullSrt)
--   assertTrue (int ≥ nullSrt)

test![TestApiBlackSort, getKind] do
  let b ← cvc5.getBooleanSort
  assertEq b.getKind SortKind.BOOLEAN_SORT
  -- let dtSort ← cvc5.createDatatypeSort -- should be (some variant of) `mkDatatypeSort`?
  -- assertEq dtSort.getKind SortKnd.DATATYPE_SORT
  let r ← cvc5.getRealSort
  let i ← cvc5.getIntegerSort
  let arr ← cvc5.mkArraySort r i
  assertEq arr.getKind SortKind.ARRAY_SORT
  let fp ← cvc5.mkFloatingPointSort 8 24
  assertEq fp.getKind SortKind.FLOATINGPOINT_SORT
  let bv ← cvc5.mkBitVectorSort 8
  assertEq bv.getKind SortKind.BITVECTOR_SORT
  let abs ← cvc5.mkAbstractSort SortKind.BITVECTOR_SORT
  assertEq abs.getKind SortKind.ABSTRACT_SORT

test![TestApiBlackSort, hasGetSymbol] do
  -- -- `null` sort not exposed
  -- let n := Srt.null ()
  let b ← cvc5.getBooleanSort
  let s0 ← cvc5.mkParamSort "s0"
  let s1 ← cvc5.mkParamSort "|s1\\|"

  -- assertError
  --   "invalid call to 'bool cvc5::Sort::hasSymbol() const', \
  --   expected non-null object"
  --   n.hasSymbol
  assertFalse (← assertOk b.hasSymbol)
  assertTrue (← assertOk s0.hasSymbol)
  assertTrue (← assertOk s1.hasSymbol)

  -- assertError
  --   "invalid call to 'std::string cvc5::Sort::getSymbol() const', \
  --   expected non-null object"
  --   n.getSymbol
  assertError
    "invalid call to 'std::string cvc5::Sort::getSymbol() const', \
    expected the sort to have a symbol."
    b.getSymbol
  assertFalse (← assertOk b.hasSymbol)
  assertEq (← assertOk s0.getSymbol) "s0"
  assertEq (← assertOk s1.getSymbol) "|s1\\|"

-- -- `null` sort not exposed
-- test![TestApiBlackSort, isNull] do
--   let n ← cvc5.Srt.null
--   assertTrue n.isNull
--   assertFalse (← cvc5.getBooleanSort).isNull

test![TestApiBlackSort, isBoolean] do
  assertTrue (← cvc5.getBooleanSort).isBoolean
  assertFalse (← cvc5.getIntegerSort).isBoolean
  -- let n ← Srt.null
  -- assertFalse n.isBoolean

test![TestApiBlackSort, isInteger] do
  assertTrue (← cvc5.getIntegerSort).isInteger
  assertFalse (← cvc5.getRealSort).isInteger
  -- let n ← Srt.null
  -- assertFalse n.isInteger

test![TestApiBlackSort, isReal] do
  assertTrue (← cvc5.getRealSort).isReal
  assertFalse (← cvc5.getIntegerSort).isReal
  -- let n ← Srt.null
  -- assertFalse n.isReal

test![TestApiBlackSort, isString] do
  assertTrue (← cvc5.getStringSort).isString
  assertFalse (← cvc5.getBooleanSort).isString
  -- let n ← Srt.null
  -- assertFalse n.isString

test![TestApiBlackSort, isRegExp] do
  assertTrue (← cvc5.getRegExpSort).isRegExp
  assertFalse (← cvc5.getStringSort).isRegExp
  -- let n ← Srt.null
  -- assertFalse n.isRegExp

test![TestApiBlackSort, isRoundingMode] do
  assertTrue (← cvc5.getRoundingModeSort).isRoundingMode
  assertFalse (← cvc5.getBooleanSort).isRoundingMode
  -- let n ← Srt.null
  -- assertFalse n.isRoundingMode

test![TestApiBlackSort, isBitVector] do
  assertTrue (← cvc5.mkBitVectorSort 8).isBitVector
  assertFalse (← cvc5.getStringSort).isBitVector
  -- let n ← Srt.null
  -- assertFalse n.isBitVector

test![TestApiBlackSort, isFiniteField] do
  assertTrue (← cvc5.mkFiniteFieldSort 7).isFiniteField
  assertFalse (← cvc5.getStringSort).isFiniteField
  -- let n ← Srt.null
  -- assertFalse n.isFiniteField

test![TestApiBlackSort, isFloatingPoint] do
  assertTrue (← cvc5.mkFloatingPointSort 8 24).isFloatingPoint
  assertFalse (← cvc5.getStringSort).isFloatingPoint
  -- let n ← Srt.null
  -- assertFalse n.isFloatingPoint

-- test![TestApiBlackSort, isDatatype] do
--   let dtSort ← cvc5.createDatatypeSort
--   assertTrue dtSort.isDatatype
--   let n ← Srt.null
--   assertFalse n.isDatatype

-- test![TestApiBlackSort, isDatatypeConstructor] do
--   let dtSort ← createDatatypeSort
--   let dt := dtSort.getDatatype
--   let consSort := dt[0].getTerm.getSort
--   -- assertError "failure" dt[3] -- not possible in lean
--   assertTrue consSort.isDatatypeConstructor
--   let n ← Srt.null
--   assertFalse n.isDatatypeConstructor

-- test![TestApiBlackSort, isDatatypeSelector] do
--   let dtSort ← cvc5.createDatatypeSort
--   let dt := dtSort.getDatatype
--   let selSort := dt[0][1].getTerm.getSort
--   -- assertError "failure" dt[0][2] -- not possible in lean
--   assertTrue selSort.isDatatypeSelector
--   let n ← Srt.null
--   assertFalse n.isDatatypeSelector

-- test![TestApiBlackSort, isDatatypeTester] do
--   let dtSort ← cvc5.createDatatypeSort
--   let dt := dtSort.getDatatype
--   let testerSort := dt[0].getTesterTerm.getSort
--   -- assertError "failure" dt[3] -- not possible in lean
--   assertTrue testerSort.isDatatypeTester
--   let n ← Srt.null
--   assertFalse n.isDatatypeTester

-- test![TestApiBlackSort, isDatatypeUpdater] do
--   let dtSort ← cvc5.createDatatypeSort
--   let dt := dtSort.getDatatype
--   let updaterSort := dt[0].getUpdaterTerm.getSort
--   -- assertError "failure" dt[3] -- not possible in lean
--   assertTrue updaterSort.isDatatypeUpdater
--   let n ← Srt.null
--   assertFalse n.isDatatypeUpdater

test![TestApiBlackSort, isFunction] do
  assertTrue (
    ← cvc5.mkFunctionSort #[← cvc5.getBooleanSort] (← cvc5.getIntegerSort)
  ).isFunction
  assertFalse (← cvc5.getStringSort).isFunction
  -- let n ← Srt.null
  -- assertFalse n.isFunction

test![TestApiBlackSort, isPredicate] do
  assertTrue (← cvc5.mkPredicateSort #[← cvc5.getRealSort]).isPredicate
  assertFalse (← cvc5.getStringSort).isPredicate
  -- let n ← Srt.null
  -- assertFalse n.isPredicate

test![TestApiBlackSort, isTuple] do
  assertTrue (← cvc5.mkTupleSort #[← cvc5.getRealSort]).isTuple
  assertFalse (← cvc5.getStringSort).isTuple
  -- let n ← Srt.null
  -- assertFalse n.isTuple

test![TestApiBlackSort, isNullable] do
  assertTrue (← cvc5.mkNullableSort (← cvc5.getRealSort)).isNullable
  assertFalse (← cvc5.getStringSort).isNullable
  -- let n ← Srt.null
  -- assertFalse n.isNullable

-- test![TestApiBlackSort, isRecord] do
--   assertEq (← cvc5.mkRecordSort #[("asdf", cvc5.getRealSort)]).isRecord true
--   let n ← Srt.null
--   assertFalse n.isRecord

test![TestApiBlackSort, isArray] do
  assertTrue (← cvc5.mkArraySort (← cvc5.getRealSort) (← cvc5.getIntegerSort)).isArray
  assertFalse (← cvc5.getStringSort).isArray
  -- let n ← Srt.null
  -- assertFalse n.isArray

test![TestApiBlackSort, isSet] do
  assertTrue (← cvc5.mkSetSort (← cvc5.getRealSort)).isSet
  assertFalse (← cvc5.getStringSort).isSet
  -- let n ← Srt.null
  -- assertFalse n.isSet

test![TestApiBlackSort, isBag] do
  assertTrue (← cvc5.mkBagSort (← cvc5.getRealSort)).isBag
  assertFalse (← cvc5.getStringSort).isBag
  -- let n ← Srt.null
  -- assertFalse n.isBag

test![TestApiBlackSort, isSequence] do
  assertTrue (← cvc5.mkSequenceSort (← cvc5.getRealSort)).isSequence
  assertFalse (← cvc5.getStringSort).isSequence
  -- let n ← Srt.null
  -- assertFalse n.isSequence

test![TestApiBlackSort, isAbstract] do
  assertTrue (← cvc5.mkAbstractSort SortKind.BITVECTOR_SORT).isAbstract
  assertFalse (← cvc5.mkAbstractSort SortKind.ARRAY_SORT).isAbstract
  assertTrue (← cvc5.mkAbstractSort SortKind.ABSTRACT_SORT).isAbstract
  -- let n ← Srt.null
  -- assertFalse n.isAbstract

test![TestApiBlackSort, isUninterpreted] do
  assertTrue (← cvc5.mkUninterpretedSort "asdf").isUninterpretedSort
  assertFalse (← cvc5.getStringSort).isUninterpretedSort
  -- let n ← Srt.null
  -- assertFalse n.isUninterpretedSort

test![TestApiBlackSort, isUninterpretedSortConstructor] do
  let scSort ← cvc5.mkUninterpretedSortConstructorSort 1 "asdf"
  assertTrue scSort.isUninterpretedSortConstructor
  let scSort2 ← cvc5.mkUninterpretedSortConstructorSort 2 "asdf"
  assertTrue scSort2.isUninterpretedSortConstructor
  assertFalse (← cvc5.getStringSort).isUninterpretedSortConstructor

-- test![TestApiBlackSort, getDatatype] do
--   let dTypeSort ← createDatatypeSort
--   assertOkDiscard dTypeSort.getDatatype
--   -- create bv sort, check should fail
--   let bvSort ← cvc5.mkBitVectorSort 32
--   assertError "failure" bvSort.getDatatype

-- test![TestApiBlackSort, datatypeSorts] do
--   let intSort := cvc5.getIntegerSort
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
--   let booleanSort := cvc5.getBooleanSort
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

-- test![TestApiBlackSort, instantiate] do
--   -- instantiate parametric datatype, check should not fail
--   let paramDTypeSort ← createParamDatatypeSort
--   assertOkDiscard (paramDTypeSort.instantiate #[cvc5.getIntegerSort])
--   -- instantiate non-parametric datatype sort, check should fail
--   let mut dTypeSpec ← cvc5.mkDatatypeDecl "list"
--   let mut cons ← cvc5.mkDatatypeConstructorDecl "cons"
--   cons := cons.addSelector "head" cvc5.getIntegerSort
--   dTypeSpec := dTypeSpec.addConstructor cons
--   let nil ← cvc5.mkDatatypeConstructorDecl "nil"
--   dTypeSpec := dTypeSpec.addConstructor nil
--   let dTypeSort ← cvc5.mkDatatypeSort dTypeSpec
--   assertError "failure" (dTypeSort.instantiate #[cvc5.getIntegerSort])
--   -- instantiate uninterpreted sort constructor
--   let sortConsSort ← cvc5.mkUninterpretedSortConstructorSort 1 "s"
--   assertOkDiscard (sortConsSort.instantiate #[cvc5.getIntegerSort])

test![TestApiBlackSort, instantiate] do
  -- let paramDTypeSort ← createParamDatatypeSort
  -- assertFalse paramDTypeSort.isInstantiated
  -- let instParamDTypeSort ← paramDTypeSort.instantiate #[cvc5.getIntegerSort]
  -- assertTrue instParamDTypeSort.isInstantiated

  let sortConsSort ← cvc5.mkUninterpretedSortConstructorSort 1 "s"
  assertFalse sortConsSort.isInstantiated
  let instSortConsSort ← sortConsSort.instantiate #[← cvc5.getIntegerSort]
  assertTrue instSortConsSort.isInstantiated

  assertFalse (← cvc5.getIntegerSort).isInstantiated
  assertFalse (← cvc5.mkBitVectorSort 32 ).isInstantiated

-- test![TestApiBlackSort, getInstantiatedParameters] do
--   let intSort := cvc5.getIntegerSort
--   let realSort := cvc5.getRealSort
--   let boolSort := cvc5.getBooleanSort
--   let bvSort ← cvc5.mkBitVectorSort 8

--   -- parametric datatype instantiation
--   let p1 := cvc5.mkParamSort "p1"
--   let p2 := cvc5.mkParamSort "p2"
--   let mut pSpec ← cvc5.mkDatatypeDecl "pdtype" #[p1, p2]
--   let mut pCons1 ← cvc5.mkDatatypeConstructorDecl "cons1"
--   let mut pCons2 ← cvc5.mkDatatypeConstructorDecl "cons2"
--   let pNil ← cvc5.mkDatatypeConstructorDecl "nil"
--   pCons1 := pCons1.addSelector "sel" p1
--   pCons2 := pCons2.addSelector "sel" p2
--   pSpec := pSpec.addConstructor pCons1
--   pSpec := pSpec.addConstructor pCons2
--   pSpec := pSpec.addConstructor pNil
--   let paramDTypeSort ← cvc5.mkDatatypeSort pSpec

--   assertError "failure" paramDTypeSort.getInstantiatedParameters

--   let instParamDTypeSort ← paramDTypeSort.instantiate #[realSort, boolSort]

--   let instSorts ← instParamDTypeSort.getInstantiatedParameters
--   assertEq instSorts[0] realSort
--   assertEq instSorts[1] boolSort

--   -- uninterpreted sort constructor sort instantiation
--   let sortConsSort ← cvc5.mkUninterpretedSortConstructorSort 4 "s"
--   assertError "failure" sortConsSort.getInstantiatedParameters

--   let instSortConsSort ← sortConsSort.instantiate #[boolSort, intSort, bvSort, realSort]

--   let instSorts ← instSortConsSort.getInstantiatedParameters
--   assertEq instSorts[0] boolSort
--   assertEq instSorts[1] intSort
--   assertEq instSorts[2] bvSort
--   assertEq instSorts[3] realSort

--   assertError "failure" intSort.getInstantiatedParameters
--   assertError "failure" bvSort.getInstantiatedParameters

test![TestApiBlackSort, getUninterpretedSortConstructor] do
  let intSort ← cvc5.getIntegerSort
  let realSort ← cvc5.getRealSort
  let boolSort ← cvc5.getBooleanSort
  let bvSort ← cvc5.mkBitVectorSort 8
  let sortConsSort ← cvc5.mkUninterpretedSortConstructorSort 4 "s"
  sortConsSort.getUninterpretedSortConstructor
  |> assertError "expected instantiated uninterpreted sort."
  let instSortConsSort ← sortConsSort.instantiate #[boolSort, intSort, bvSort, realSort]
  assertEq sortConsSort (← instSortConsSort.getUninterpretedSortConstructor)

test![TestApiBlackSort, getFunctionArity] do
  let funSort ← cvc5.mkFunctionSort #[← cvc5.mkUninterpretedSort "u"] (← cvc5.getIntegerSort)
  assertEq (← funSort.getFunctionArity) 1
  let bvSort ← cvc5.mkBitVectorSort 32
  assertError "not a function sort: (_ BitVec 32)" bvSort.getFunctionArity

test![TestApiBlackSort, getFunctionDomainSorts] do
  let funSort ← cvc5.mkFunctionSort #[← cvc5.mkUninterpretedSort "u"] (← cvc5.getIntegerSort)
  assertOkDiscard funSort.getFunctionDomainSorts
  let bvSort ← cvc5.mkBitVectorSort 32
  assertError "not a function sort: (_ BitVec 32)" bvSort.getFunctionDomainSorts

test![TestApiBlackSort, getFunctionCodomainSort] do
  let funSort ← cvc5.mkFunctionSort #[← cvc5.mkUninterpretedSort "u"] (← cvc5.getIntegerSort)
  assertOkDiscard funSort.getFunctionCodomainSort
  let bvSort ← cvc5.mkBitVectorSort 32
  assertError "not a function sort(_ BitVec 32)" bvSort.getFunctionCodomainSort

test![TestApiBlackSort, getArrayIndexSort] do
  let elementSort ← cvc5.mkBitVectorSort 32
  let indexSort ← cvc5.mkBitVectorSort 32
  let arraySort ← cvc5.mkArraySort indexSort elementSort
  assertOkDiscard arraySort.getArrayIndexSort
  assertError "not an array sort." indexSort.getArrayIndexSort

test![TestApiBlackSort, getArrayElementSort] do
  let elementSort ← cvc5.mkBitVectorSort 32
  let indexSort ← cvc5.mkBitVectorSort 32
  let arraySort ← cvc5.mkArraySort indexSort elementSort
  assertOkDiscard arraySort.getArrayElementSort
  assertError "not an array sort." indexSort.getArrayElementSort

test![TestApiBlackSort, getSetElementSort] do
  let setSort ← cvc5.mkSetSort (← cvc5.getIntegerSort)
  let elementSort ← assertOk setSort.getSetElementSort
  assertEq elementSort (← cvc5.getIntegerSort)
  let bvSort ← cvc5.mkBitVectorSort 32
  assertError "not a set sort." bvSort.getSetElementSort

test![TestApiBlackSort, getBagElementSort] do
  let bagSort ← cvc5.mkBagSort (← cvc5.getIntegerSort)
  let elementSort ← assertOk bagSort.getBagElementSort
  assertEq elementSort (← cvc5.getIntegerSort)
  let bvSort ← cvc5.mkBitVectorSort 32
  assertError "not a bag sort." bvSort.getBagElementSort

test![TestApiBlackSort, getSequenceElementSort] do
  let seqSort ← cvc5.mkSequenceSort (← cvc5.getIntegerSort)
  let elementSort ← assertOk seqSort.getSequenceElementSort
  assertEq elementSort (← cvc5.getIntegerSort)
  let bvSort ← cvc5.mkBitVectorSort 32
  assertError "not a sequence sort." bvSort.getSequenceElementSort

test![TestApiBlackSort, getAbstractedKind] do
  assertEq
    (← (← cvc5.mkAbstractSort SortKind.BITVECTOR_SORT).getAbstractedKind)
    SortKind.BITVECTOR_SORT
  -- `?Array` is syntax sugar for `(Array ? ?)`, thus the constructed sort is an `Array` sort, not
  -- an abstract sort and its abstract kind cannot be extracted
  assertError "not an abstract sort." (do
    let absSort ← cvc5.mkAbstractSort SortKind.ARRAY_SORT
    absSort.getAbstractedKind
  )
  assertEq
    (← (← cvc5.mkAbstractSort SortKind.ABSTRACT_SORT).getAbstractedKind)
    SortKind.ABSTRACT_SORT

test![TestApiBlackSort, getSymbol] do
  let uSort ← cvc5.mkUninterpretedSort "u"
  assertEq (← uSort.getSymbol) "u"
  let bvSort ← cvc5.mkBitVectorSort 32
  assertError
    "invalid call to 'std::string cvc5::Sort::getSymbol() const', \
    expected the sort to have a symbol."
    bvSort.getSymbol

test![TestApiBlackSort, getUninterpretedSortConstructorName] do
  let sSort ← cvc5.mkUninterpretedSortConstructorSort 2 "s"
  assertEq (← sSort.getSymbol) "s"
  let bvSort ← cvc5.mkBitVectorSort 32
  assertError
    "invalid call to 'std::string cvc5::Sort::getSymbol() const', \
    expected the sort to have a symbol."
    bvSort.getSymbol

test![TestApiBlackSort, getUninterpretedSortConstructorArity] do
  let sSort ← cvc5.mkUninterpretedSortConstructorSort 2 "s"
  assertEq (← sSort.getUninterpretedSortConstructorArity) 2
  let bvSort ← cvc5.mkBitVectorSort 32
  assertError
    "not a sort constructor sort."
    bvSort.getUninterpretedSortConstructorArity

test![TestApiBlackSort, getBitVectorSize] do
  let bvSort ← cvc5.mkBitVectorSort 32
  assertEq (← bvSort.getBitVectorSize) 32
  let setSort ← cvc5.mkSetSort (← cvc5.getIntegerSort)
  assertError "not a bit-vector sort." setSort.getBitVectorSize

test![TestApiBlackSort, getFiniteFieldSize] do
  let ffSort ← cvc5.mkFiniteFieldSort 31
  assertOkDiscard ffSort.getFiniteFieldSize
  assertEq (← ffSort.getFiniteFieldSize) 31
  -- let n ← Srt.null
  -- n.getFiniteFieldSize |> assertError
  --   "invalid call to 'std::string cvc5::Sort::getFiniteFieldSize() const', \
  --   expected non-null object"

test![TestApiBlackSort, getFloatingPointExponentSize] do
  let fpSort ← cvc5.mkFloatingPointSort 4 8
  assertEq (← fpSort.getFloatingPointExponentSize) 4
  let setSort ← cvc5.getIntegerSort >>= cvc5.mkSetSort
  assertError "not a floating-point sort." setSort.getFloatingPointExponentSize

test![TestApiBlackSort, getFloatingPointSignificandSize] do
  let fpSort ← cvc5.mkFloatingPointSort 4 8
  assertEq (← fpSort.getFloatingPointSignificandSize) 8
  let setSort ← cvc5.getIntegerSort >>= cvc5.mkSetSort
  assertError "not a floating-point sort." setSort.getFloatingPointSignificandSize

-- test![TestApiBlackSort, getDatatypeArity] do
--   -- create datatype sort, check should not fail
--   let mut dTypeSpec ← cvc5.mkDatatypeDecl "list"
--   let mut cons ← cvc5.mkDatatypeConstructorDecl "cons"
--   cons := addSelector "head" cvc5.getIntegerSort
--   dTypeSpec := dTypeSpec.addConstructor cons
--   let nil ← cvc5.mkDatatypeConstructorDecl "nil"
--   dTypeSpec := dTypeSpec.addConstructor nil
--   let dTypeSort ← cvc5.mkDatatypeSort dTypeSpec
--   assertOkDiscard dTypeSort.getDatatypeArity
--   -- create bv sort, check should fail
--   let bvSort ← cvc5.mkBitVectorSort 32
--   assertError "failure" bvSort.getDatatypeArity

test![TestApiBlackSort, getTupleLength] do
  let tupleSort ← cvc5.mkTupleSort #[← cvc5.getIntegerSort, ← cvc5.getIntegerSort]
  assertEq (← tupleSort.getTupleLength) 2
  let bvSort ← cvc5.mkBitVectorSort 32
  assertError "not a tuple sort." bvSort.getTupleLength

test![TestApiBlackSort, getTupleSorts] do
  let tupleSort ← cvc5.mkTupleSort #[← cvc5.getIntegerSort, ← cvc5.getIntegerSort]
  assertOkDiscard tupleSort.getTupleSorts
  let bvSort ← cvc5.mkBitVectorSort 32
  assertError "not a tuple sort." bvSort.getTupleSorts

test![TestApiBlackSort, getNullableElementSort] do
  let nullableSort ← cvc5.mkNullableSort (← cvc5.getIntegerSort)
  assertOkDiscard nullableSort.getNullableElementSort
  let elementSort ← nullableSort.getNullableElementSort
  assertEq elementSort (← cvc5.getIntegerSort)
  let bvSort ← cvc5.mkBitVectorSort 32
  assertError "not a nullable sort." bvSort.getNullableElementSort

test![TestApiBlackSort, sortCompare] do
  let boolSort ← cvc5.getBooleanSort
  let intSort ← cvc5.getIntegerSort
  let bvSort ← cvc5.mkBitVectorSort 32
  let bvSort2 ← cvc5.mkBitVectorSort 32
  assertTrue (bvSort ≥ bvSort2)
  assertTrue (bvSort ≤ bvSort2)
  assertTrue ((intSort > boolSort) ≠ (intSort < boolSort))
  assertTrue ((intSort > bvSort ∨ intSort == bvSort) = (intSort ≥ bvSort))

test![TestApiBlackSort, sortScopedToString] do
  let name := "uninterp-sort"
  let bvSort8 ← cvc5.mkBitVectorSort 8
  let uSort ← cvc5.mkUninterpretedSort name
  -- repetition present in the original test
  assertEq bvSort8.toString "(_ BitVec 8)"
  assertEq uSort.toString name
  assertEq bvSort8.toString "(_ BitVec 8)"
  assertEq uSort.toString name

-- -- `null` sort not exposed
-- test![TestApiBlackSort, toString] do
--   assertOkDiscard (toString <$> Srt.null)

test![TestApiBlackSort, substitute] do
  let sortVar0 ← cvc5.mkParamSort "T0"
  let sortVar1 ← cvc5.mkParamSort "T1"
  let intSort ← cvc5.getIntegerSort
  let realSort ← cvc5.getRealSort
  let arraySort0 ← cvc5.mkArraySort sortVar0 sortVar0
  let arraySort1 ← cvc5.mkArraySort sortVar0 sortVar1
  -- now create instantiations of the defined sorts
  assertOkDiscard
    (arraySort0.substitute #[sortVar0] #[intSort])
  assertOkDiscard
    (arraySort1.substitute #[sortVar0, sortVar1] #[intSort, realSort])
