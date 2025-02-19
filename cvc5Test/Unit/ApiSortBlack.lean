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
  -- let dtSort ← tm.createDatatypeSort
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
