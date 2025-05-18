import cvc5Test.Init

/-! # Black box testing of the `Op` type

- <https://github.com/cvc5/cvc5/blob/main/test/unit/api/cpp/api_sort_kind_black.cpp>
-/

namespace cvc5.Test

test![TestApiSortKind, sortKindToString] _tm => do
  let mut skStr := ""
  for sk in SortKind.listAll do
    skStr := toString sk
    if sk = SortKind.INTERNAL_SORT_KIND then
      assertEq skStr "INTERNAL_SORT_KIND"
    else if sk = SortKind.UNDEFINED_SORT_KIND then
      assertEq skStr "UNDEFINED_SORT_KIND"
    else
      assertNe skStr "UNDEFINED_SORT_KIND"
      assertNe skStr "INTERNAL_SORT_KIND"
  assertTrue true
