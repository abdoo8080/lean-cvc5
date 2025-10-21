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

open Env

test![TestApiBlackSort, hash] do
  assertEq (← getIntegerSort).hash (← getIntegerSort).hash
  assertNe (← getIntegerSort).hash (← getStringSort).hash

test![TestApiBlackSort, operatorsComparison] do
  assertFalse <| (← getIntegerSort) == Sort.null ()
  assertTrue <| (← getIntegerSort) != Sort.null ()
  assertFalse <| (← getIntegerSort) < Sort.null ()
  assertFalse <| (← getIntegerSort) ≤ Sort.null ()
  assertTrue <| (← getIntegerSort) > Sort.null ()
  assertTrue <| (← getIntegerSort) ≥ Sort.null ()

test![TestApiBlackSort, getKind] do
  let b ← getBooleanSort
  assertEq b.getKind SortKind.BOOLEAN_SORT
  -- let dtSort ← tm.createDatatypeSort -- should be (some variant of) `mkDatatypeSort`?
  -- assertEq dtSort.getKind SortKnd.DATATYPE_SORT
  let r ← getRealSort
  let i ← getIntegerSort
  let arr ← mkArraySort r i
  assertEq arr.getKind SortKind.ARRAY_SORT
  let fp ← mkFloatingPointSort 8 24
  assertEq fp.getKind SortKind.FLOATINGPOINT_SORT
  let bv ← mkBitVectorSort 8
  assertEq bv.getKind SortKind.BITVECTOR_SORT
  let abs ← mkAbstractSort SortKind.BITVECTOR_SORT
  assertEq abs.getKind SortKind.ABSTRACT_SORT

test![TestApiBlackSort, hasGetSymbol] do
  let n := cvc5.Sort.null ()
  let b ← getBooleanSort
  let s0 ← mkParamSort "s0"
  let s1 ← mkParamSort "|s1\\|"

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

test![TestApiBlackSort, isNull] do
  let n := cvc5.Sort.null ()
  assertTrue n.isNull
  assertFalse (← getBooleanSort).isNull

test![TestApiBlackSort, isBoolean] do
  assertTrue (← getBooleanSort).isBoolean
  let n := cvc5.Sort.null ()
  assertFalse n.isBoolean

test![TestApiBlackSort, isInteger] do
  assertTrue (← getIntegerSort).isInteger
  assertFalse (← getRealSort).isInteger
  let n := cvc5.Sort.null ()
  assertFalse n.isInteger

test![TestApiBlackSort, isReal] do
  assertTrue (← getRealSort).isReal
  assertFalse (← getIntegerSort).isReal
  let n := cvc5.Sort.null ()
  assertFalse n.isReal

test![TestApiBlackSort, isString] do
  assertTrue (← getStringSort).isString
  let n := cvc5.Sort.null ()
  assertFalse n.isString

test![TestApiBlackSort, isRegExp] do
  assertTrue (← getRegExpSort).isRegExp
  let n := cvc5.Sort.null ()
  assertFalse n.isRegExp

test![TestApiBlackSort, isRoundingMode] do
  assertTrue (← getRoundingModeSort).isRoundingMode
  let n := cvc5.Sort.null ()
  assertFalse n.isRoundingMode

test![TestApiBlackSort, isBitVector] do
  assertTrue (← mkBitVectorSort 8).isBitVector
  let n := cvc5.Sort.null ()
  assertFalse n.isBitVector

test![TestApiBlackSort, isFiniteField] do
  assertTrue (← mkFiniteFieldSort 7).isFiniteField
  let n := cvc5.Sort.null ()
  assertFalse n.isFiniteField

test![TestApiBlackSort, isFloatingPoint] do
  assertTrue (← mkFloatingPointSort 8 24).isFloatingPoint
  let n := cvc5.Sort.null ()
  assertFalse n.isFloatingPoint

-- test![TestApiBlackSort, isDatatype] do
--   let dtSort ← createDatatypeSort
--   assertTrue dtSort.isDatatype
--   let n := cvc5.Sort.null ()
--   assertFalse n.isDatatype

-- test![TestApiBlackSort, isDatatypeConstructor] do
--   let dtSort ← createDatatypeSort
--   let dt := dtSort.getDatatype
--   let consSort := dt[0].getTerm.getSort
--   -- assertError "failure" dt[3] -- not possible in lean
--   assertTrue consSort.isDatatypeConstructor
--   let n := cvc5.Sort.null ()
--   assertFalse n.isDatatypeConstructor

-- test![TestApiBlackSort, isDatatypeSelector] do
--   let dtSort ← createDatatypeSort
--   let dt := dtSort.getDatatype
--   let selSort := dt[0][1].getTerm.getSort
--   -- assertError "failure" dt[0][2] -- not possible in lean
--   assertTrue selSort.isDatatypeSelector
--   let n := cvc5.Sort.null ()
--   assertFalse n.isDatatypeSelector

-- test![TestApiBlackSort, isDatatypeTester] do
--   let dtSort ← createDatatypeSort
--   let dt := dtSort.getDatatype
--   let testerSort := dt[0].getTesterTerm.getSort
--   -- assertError "failure" dt[3] -- not possible in lean
--   assertTrue testerSort.isDatatypeTester
--   let n := cvc5.Sort.null ()
--   assertFalse n.isDatatypeTester

-- test![TestApiBlackSort, isDatatypeUpdater] do
--   let dtSort ← createDatatypeSort
--   let dt := dtSort.getDatatype
--   let updaterSort := dt[0].getUpdaterTerm.getSort
--   -- assertError "failure" dt[3] -- not possible in lean
--   assertTrue updaterSort.isDatatypeUpdater
--   let n := cvc5.Sort.null ()
--   assertFalse n.isDatatypeUpdater

test![TestApiBlackSort, isFunction] do
  assertTrue (← mkFunctionSort #[← getBooleanSort] (← getIntegerSort)).isFunction
  let n := cvc5.Sort.null ()
  assertFalse n.isFunction

test![TestApiBlackSort, isPredicate] do
  assertTrue (← mkPredicateSort #[← getRealSort]).isPredicate
  let n := cvc5.Sort.null ()
  assertFalse n.isPredicate

test![TestApiBlackSort, isTuple] do
  assertTrue (← mkTupleSort #[← getRealSort]).isTuple
  let n := cvc5.Sort.null ()
  assertFalse n.isTuple

test![TestApiBlackSort, isNullable] do
  assertTrue (← mkNullableSort (← getRealSort)).isNullable
  let n := cvc5.Sort.null ()
  assertFalse n.isNullable

-- test![TestApiBlackSort, isRecord] do
--   assertEq (← mkRecordSort #[("asdf", ← getRealSort)]).isRecord true
--   let n := cvc5.Sort.null ()
--   assertFalse n.isRecord

test![TestApiBlackSort, isArray] do
  assertTrue (← mkArraySort (← getRealSort) (← getIntegerSort)).isArray
  let n := cvc5.Sort.null ()
  assertFalse n.isArray

test![TestApiBlackSort, isSet] do
  assertTrue (← mkSetSort (← getRealSort)).isSet
  let n := cvc5.Sort.null ()
  assertFalse n.isSet

test![TestApiBlackSort, isBag] do
  assertTrue (← mkBagSort (← getRealSort)).isBag
  let n := cvc5.Sort.null ()
  assertFalse n.isBag

test![TestApiBlackSort, isSequence] do
  assertTrue (← mkSequenceSort (← getRealSort)).isSequence
  let n := cvc5.Sort.null ()
  assertFalse n.isSequence

test![TestApiBlackSort, isAbstract] do
  assertTrue (← mkAbstractSort SortKind.BITVECTOR_SORT).isAbstract
  assertFalse (← mkAbstractSort SortKind.ARRAY_SORT).isAbstract
  assertTrue (← mkAbstractSort SortKind.ABSTRACT_SORT).isAbstract
  let n := cvc5.Sort.null ()
  assertFalse n.isAbstract

test![TestApiBlackSort, isUninterpreted] do
  assertTrue (← mkUninterpretedSort "asdf").isUninterpretedSort
  let n := cvc5.Sort.null ()
  assertFalse n.isUninterpretedSort

test![TestApiBlackSort, isUninterpretedSortConstructor] do
  let scSort ← mkUninterpretedSortConstructorSort 1 "asdf"
  assertTrue scSort.isUninterpretedSortConstructor
  let scSort2 ← mkUninterpretedSortConstructorSort 2 "asdf"
  assertTrue scSort2.isUninterpretedSortConstructor

-- test![TestApiBlackSort, getDatatype] do
--   let dTypeSort ← createDatatypeSort
--   assertOkDiscard dTypeSort.getDatatype
--   -- create bv sort, check should fail
--   let bvSort ← mkBitVectorSort 32
--   assertError "failure" bvSort.getDatatype

-- test![TestApiBlackSort, datatypeSorts] do
--   let intSort ← getIntegerSort
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
--   let booleanSort ← getBooleanSort
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
--   assertOkDiscard (paramDTypeSort.instantiate #[getIntegerSort])
--   -- instantiate non-parametric datatype sort, check should fail
--   let mut dTypeSpec ← mkDatatypeDecl "list"
--   let mut cons ← mkDatatypeConstructorDecl "cons"
--   cons := cons.addSelector "head" getIntegerSort
--   dTypeSpec := dTypeSpec.addConstructor cons
--   let nil ← mkDatatypeConstructorDecl "nil"
--   dTypeSpec := dTypeSpec.addConstructor nil
--   let dTypeSort ← mkDatatypeSort dTypeSpec
--   assertError "failure" (dTypeSort.instantiate #[getIntegerSort])
--   -- instantiate uninterpreted sort constructor
--   let sortConsSort ← mkUninterpretedSortConstructorSort 1 "s"
--   assertOkDiscard (sortConsSort.instantiate #[tm.getIntegerSort])

test![TestApiBlackSort, instantiate] do
  -- let paramDTypeSort ← createParamDatatypeSort
  -- assertFalse paramDTypeSort.isInstantiated
  -- let instParamDTypeSort ← paramDTypeSort.instantiate #[tm.getIntegerSort]
  -- assertTrue instParamDTypeSort.isInstantiated

  let sortConsSort ← mkUninterpretedSortConstructorSort 1 "s"
  assertFalse sortConsSort.isInstantiated
  let instSortConsSort ← sortConsSort.instantiate #[← getIntegerSort]
  assertTrue instSortConsSort.isInstantiated

  assertFalse (← getIntegerSort).isInstantiated
  assertFalse (← mkBitVectorSort 32 ).isInstantiated

-- test![TestApiBlackSort, getInstantiatedParameters] do
--   let intSort ← getIntegerSort
--   let realSort ← getRealSort
--   let boolSort ← getBooleanSort
--   let bvSort ← tm.mkBitVectorSort 8

--   -- parametric datatype instantiation
--   let p1 ← mkParamSort "p1"
--   let p2 ← mkParamSort "p2"
--   let mut pSpec ← mkDatatypeDecl "pdtype" #[p1, p2]
--   let mut pCons1 ← mkDatatypeConstructorDecl "cons1"
--   let mut pCons2 ← mkDatatypeConstructorDecl "cons2"
--   let pNil ← mkDatatypeConstructorDecl "nil"
--   pCons1 := pCons1.addSelector "sel" p1
--   pCons2 := pCons2.addSelector "sel" p2
--   pSpec := pSpec.addConstructor pCons1
--   pSpec := pSpec.addConstructor pCons2
--   pSpec := pSpec.addConstructor pNil
--   let paramDTypeSort ← mkDatatypeSort pSpec

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

test![TestApiBlackSort, getUninterpretedSortConstructor] do
  let intSort ← getIntegerSort
  let realSort ← getRealSort
  let boolSort ← getBooleanSort
  let bvSort ← mkBitVectorSort 8
  let sortConsSort ← mkUninterpretedSortConstructorSort 4 "s"
  sortConsSort.getUninterpretedSortConstructor
  |> assertError "expected instantiated uninterpreted sort."
  let instSortConsSort ← sortConsSort.instantiate #[boolSort, intSort, bvSort, realSort]
  assertEq sortConsSort (← instSortConsSort.getUninterpretedSortConstructor)

test![TestApiBlackSort, getFunctionArity] do
  let funSort ← mkFunctionSort #[← mkUninterpretedSort "u"] (← getIntegerSort)
  assertEq (← funSort.getFunctionArity) 1
  let bvSort ← mkBitVectorSort 32
  assertError "not a function sort: (_ BitVec 32)" bvSort.getFunctionArity

test![TestApiBlackSort, getFunctionDomainSorts] do
  let funSort ← mkFunctionSort #[← mkUninterpretedSort "u"] (← getIntegerSort)
  assertOkDiscard funSort.getFunctionDomainSorts
  let bvSort ← mkBitVectorSort 32
  assertError "not a function sort: (_ BitVec 32)" bvSort.getFunctionDomainSorts

test![TestApiBlackSort, getFunctionCodomainSort] do
  let funSort ← mkFunctionSort #[← mkUninterpretedSort "u"] (← getIntegerSort)
  assertOkDiscard funSort.getFunctionCodomainSort
  let bvSort ← mkBitVectorSort 32
  assertError "not a function sort(_ BitVec 32)" bvSort.getFunctionCodomainSort

test![TestApiBlackSort, getArrayIndexSort] do
  let elementSort ← mkBitVectorSort 32
  let indexSort ← mkBitVectorSort 32
  let arraySort ← mkArraySort indexSort elementSort
  assertOkDiscard arraySort.getArrayIndexSort
  assertError "not an array sort." indexSort.getArrayIndexSort

test![TestApiBlackSort, getArrayElementSort] do
  let elementSort ← mkBitVectorSort 32
  let indexSort ← mkBitVectorSort 32
  let arraySort ← mkArraySort indexSort elementSort
  assertOkDiscard arraySort.getArrayElementSort
  assertError "not an array sort." indexSort.getArrayElementSort

test![TestApiBlackSort, getSetElementSort] do
  let setSort ← mkSetSort (← getIntegerSort)
  let elementSort ← assertOk setSort.getSetElementSort
  assertEq elementSort (← getIntegerSort)
  let bvSort ← mkBitVectorSort 32
  assertError "not a set sort." bvSort.getSetElementSort

test![TestApiBlackSort, getBagElementSort] do
  let bagSort ← mkBagSort (← getIntegerSort)
  let elementSort ← assertOk bagSort.getBagElementSort
  assertEq elementSort (← getIntegerSort)
  let bvSort ← mkBitVectorSort 32
  assertError "not a bag sort." bvSort.getBagElementSort

test![TestApiBlackSort, getSequenceElementSort] do
  let seqSort ← mkSequenceSort (← getIntegerSort)
  let elementSort ← assertOk seqSort.getSequenceElementSort
  assertEq elementSort (← getIntegerSort)
  let bvSort ← mkBitVectorSort 32
  assertError "not a sequence sort." bvSort.getSequenceElementSort

test![TestApiBlackSort, getAbstractedKind] do
  assertEq
    (← (← mkAbstractSort SortKind.BITVECTOR_SORT).getAbstractedKind)
    SortKind.BITVECTOR_SORT
  -- `?Array` is syntax sugar for `(Array ? ?)`, thus the constructed sort is an `Array` sort, not
  -- an abstract sort and its abstract kind cannot be extracted
  assertError "not an abstract sort." (do
    let absSort ← mkAbstractSort SortKind.ARRAY_SORT
    absSort.getAbstractedKind
  )
  assertEq
    (← (← mkAbstractSort SortKind.ABSTRACT_SORT).getAbstractedKind)
    SortKind.ABSTRACT_SORT

test![TestApiBlackSort, getSymbol] do
  let uSort ← mkUninterpretedSort "u"
  assertEq (← uSort.getSymbol) "u"
  let bvSort ← mkBitVectorSort 32
  assertError
    "invalid call to 'std::string cvc5::Sort::getSymbol() const', \
    expected the sort to have a symbol."
    bvSort.getSymbol

test![TestApiBlackSort, getUninterpretedSortConstructorName] do
  let sSort ← mkUninterpretedSortConstructorSort 2 "s"
  assertEq (← sSort.getSymbol) "s"
  let bvSort ← mkBitVectorSort 32
  assertError
    "invalid call to 'std::string cvc5::Sort::getSymbol() const', \
    expected the sort to have a symbol."
    bvSort.getSymbol

test![TestApiBlackSort, getUninterpretedSortConstructorArity] do
  let sSort ← mkUninterpretedSortConstructorSort 2 "s"
  assertEq (← sSort.getUninterpretedSortConstructorArity) 2
  let bvSort ← mkBitVectorSort 32
  assertError
    "not a sort constructor sort."
    bvSort.getUninterpretedSortConstructorArity

test![TestApiBlackSort, getBitVectorSize] do
  let bvSort ← mkBitVectorSort 32
  assertEq (← bvSort.getBitVectorSize) 32
  let setSort ← mkSetSort (← getIntegerSort)
  assertError "not a bit-vector sort." setSort.getBitVectorSize

test![TestApiBlackSort, getFiniteFieldSize] do
  let ffSort ← mkFiniteFieldSort 31
  assertOkDiscard ffSort.getFiniteFieldSize
  assertEq (← ffSort.getFiniteFieldSize) 31
  (cvc5.Sort.null ()).getFiniteFieldSize |> assertError
    "invalid call to 'std::string cvc5::Sort::getFiniteFieldSize() const', \
    expected non-null object"

test![TestApiBlackSort, getFloatingPointExponentSize] do
  let fpSort ← mkFloatingPointSort 4 8
  assertEq (← fpSort.getFloatingPointExponentSize) 4
  let setSort ← mkSetSort (← getIntegerSort)
  assertError "not a floating-point sort." setSort.getFloatingPointExponentSize

test![TestApiBlackSort, getFloatingPointSignificandSize] do
  let fpSort ← mkFloatingPointSort 4 8
  assertEq (← fpSort.getFloatingPointSignificandSize) 8
  let setSort ← mkSetSort (← getIntegerSort)
  assertError "not a floating-point sort." setSort.getFloatingPointSignificandSize

-- test![TestApiBlackSort, getDatatypeArity] do
--   -- create datatype sort, check should not fail
--   let mut dTypeSpec ← mkDatatypeDecl "list"
--   let mut cons ← mkDatatypeConstructorDecl "cons"
--   cons := addSelector "head" (← getIntegerSort)
--   dTypeSpec := dTypeSpec.addConstructor cons
--   let nil ← mkDatatypeConstructorDecl "nil"
--   dTypeSpec := dTypeSpec.addConstructor nil
--   let dTypeSort ← mkDatatypeSort dTypeSpec
--   assertOkDiscard dTypeSort.getDatatypeArity
--   -- create bv sort, check should fail
--   let bvSort ← mkBitVectorSort 32
--   assertError "failure" bvSort.getDatatypeArity

test![TestApiBlackSort, getTupleLength] do
  let tupleSort ← mkTupleSort #[← getIntegerSort, ← getIntegerSort]
  assertEq (← tupleSort.getTupleLength) 2
  let bvSort ← mkBitVectorSort 32
  assertError "not a tuple sort." bvSort.getTupleLength

test![TestApiBlackSort, getTupleSorts] do
  let tupleSort ← mkTupleSort #[← getIntegerSort, ← getIntegerSort]
  assertOkDiscard tupleSort.getTupleSorts
  let bvSort ← mkBitVectorSort 32
  assertError "not a tuple sort." bvSort.getTupleSorts

test![TestApiBlackSort, getNullableElementSort] do
  let nullableSort ← mkNullableSort (← getIntegerSort)
  assertOkDiscard nullableSort.getNullableElementSort
  let elementSort ← nullableSort.getNullableElementSort
  assertEq elementSort (← getIntegerSort)
  let bvSort ← mkBitVectorSort 32
  assertError "not a nullable sort." bvSort.getNullableElementSort

test![TestApiBlackSort, sortCompare] do
  let boolSort ← getBooleanSort
  let intSort ← getIntegerSort
  let bvSort ← mkBitVectorSort 32
  let bvSort2 ← mkBitVectorSort 32
  assertTrue (bvSort ≥ bvSort2)
  assertTrue (bvSort ≤ bvSort2)
  assertTrue ((intSort > boolSort) ≠ (intSort < boolSort))
  assertTrue ((intSort > bvSort ∨ intSort == bvSort) = (intSort ≥ bvSort))

test![TestApiBlackSort, sortScopedToString] do
  let name := "uninterp-sort"
  let bvSort8 ← mkBitVectorSort 8
  let uSort ← mkUninterpretedSort name
  -- repetition present in the original test
  assertEq bvSort8.toString "(_ BitVec 8)"
  assertEq uSort.toString name
  assertEq bvSort8.toString "(_ BitVec 8)"
  assertEq uSort.toString name

test![TestApiBlackSort, toString] do
  -- useless test here, as `toString` is not expected to fail at all
  assertOkDiscard (return (Sort.null ()).toString)

test![TestApiBlackSort, substitute] do
  let sortVar0 ← mkParamSort "T0"
  let sortVar1 ← mkParamSort "T1"
  let intSort ← getIntegerSort
  let realSort ← getRealSort
  let arraySort0 ← mkArraySort sortVar0 sortVar0
  let arraySort1 ← mkArraySort sortVar0 sortVar1
  -- now create instantiations of the defined sorts
  assertOkDiscard
    (arraySort0.substitute #[sortVar0] #[intSort])
  assertOkDiscard
    (arraySort1.substitute #[sortVar0, sortVar1] #[intSort, realSort])
