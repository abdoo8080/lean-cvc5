import cvc5Test.Init

/-! # Black box testing of the `Op` type

- <https://github.com/cvc5/cvc5/blob/main/test/unit/api/cpp/api_kind_black.cpp>
-/

namespace cvc5.Test

test![TestApiKind, kindToString] do
  for idx in [Kind.INTERNAL_KIND.ctorIdx : Kind.LAST_KIND.ctorIdx] do
    let k := Kind.ofNat idx
    -- if this assertion fails, `s_kinds` in `cvc5.cpp` is missing kind `k`.
    assertNe k.toString "?"

test![TestApiKind, kindHash] do
  -- assertion failures here indicate a problem in lean-to-cpp conversion
  for idx in [Kind.INTERNAL_KIND.ctorIdx : Kind.LAST_KIND.ctorIdx] do
    let k := Kind.ofNat idx
    if k = Kind.INTERNAL_KIND then
      assertEq (k.hash + 2) ⟨UInt64.size⟩
    else if k  = Kind.UNDEFINED_KIND then
      assertEq (k.hash + 1) ⟨UInt64.size⟩
    else
      assertEq (k.hash + 2) ⟨k.ctorIdx⟩
