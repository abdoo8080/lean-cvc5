import Cvc5Test.Init

namespace cvc5.Test

/-! White box testing of the Term class.

- <https://github.com/cvc5/cvc5/blob/51aba8330d5766ff8c5440a87e7380901ef582f1/test/unit/api/cpp/api_term_white.cpp>
-/

/-- info: -/
#guard_msgs in #eval IO.run do
  let tm ← TermManager.new

  let intSort := tm.getIntegerSort
  let bvSort := tm.mkBitVectorSort! 8;
  let arrSort := tm.mkArraySort! bvSort intSort;
  let funSort := tm.mkFunctionSort! #[intSort] bvSort;

  let x := tm.mkConst intSort "x"
  let a := tm.mkConst arrSort "a"
  let b := tm.mkConst bvSort "b"

  let ab := tm.mkTerm! .SELECT #[a, b]
  -- let ext := tm.mkOpOfIndices .BITVECTOR_EXTRACT #[4, 0]
  -- let extb := tm.mkTermOfOp ext #[b]

  assertEq ab.getOp (tm.mkOpOfIndices! .SELECT #[])

  let f := tm.mkConst funSort "f"
  let fx := tm.mkTerm! .APPLY_UF #[f, x]

  assertEq fx.getOp (tm.mkOpOfIndices! .APPLY_UF #[])
