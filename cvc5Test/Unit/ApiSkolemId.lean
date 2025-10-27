import cvc5Test.Init

/-! # Black box testing of the `Op` type

- <https://github.com/cvc5/cvc5/blob/main/test/unit/api/cpp/api_skolem_id_black.cpp>
-/

namespace cvc5.Test

test![TestApiBlackSkolemId, skolemIdToString] do
  for idx in [SkolemId.INTERNAL.toCtorIdx : SkolemId.NONE.toCtorIdx] do
    let si := SkolemId.ofNat idx
    -- if this assertion fails, the switch in `enum_to_string.cpp` is missing id `si`.
    assertNe si.toString "?"

test![TestApiBlackSkolemId, skolemIdHash] do
  for idx in [SkolemId.INTERNAL.toCtorIdx : SkolemId.NONE.toCtorIdx] do
    let si := SkolemId.ofNat idx
    assertEq si.hash ⟨si.toCtorIdx⟩
  assertNe SkolemId.PURIFY.hash SkolemId.INTERNAL.hash
