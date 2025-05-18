import cvc5Test.Init

/-! # Black box testing of the `Op` type

- <https://github.com/cvc5/cvc5/blob/main/test/unit/api/cpp/api_skolem_id_black.cpp>
-/

namespace cvc5.Test

test![TestApiBlackSkolemId, skolemIdToString] _tm => do
  for si in SkolemId.listAll do
    -- if this assertion fails, the switch in `enum_to_string.cpp` is missing id `si`.
    assertNe si.toString "?"

test![TestApiBlackSkolemId, skolemIdHash] _tm => do
  assertEq SkolemId.PURIFY.hash SkolemId.PURIFY.toCtorIdx
  assertNe SkolemId.INTERNAL.hash SkolemId.PURIFY.toCtorIdx
