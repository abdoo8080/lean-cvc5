import cvc5Test.Init

/-! # Black box testing of the `Op` type

- <https://github.com/cvc5/cvc5/blob/main/test/unit/api/cpp/api_kind_black.cpp>
-/

namespace cvc5.Test

test![TestApiKind, kindToString] _tm => do
  for k in Kind.listAll do
    -- if this assertion fails, `s_kinds` in `cvc5.cpp` is missing kind `k`.
    assertNe k.toString "?"
