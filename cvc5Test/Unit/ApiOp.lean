import cvc5Test.Init

/-! # Black box testing of the `Op` type

- <https://github.com/cvc5/cvc5/blob/main/test/unit/api/cpp/api_op_black.cpp>
-/

namespace cvc5.Test

open Env

test! do
  let bv1 ←
    mkOp Kind.BITVECTOR_EXTRACT #[31, 1]
    |> assertOk
  let bv1' ←
    mkOp Kind.BITVECTOR_EXTRACT #[31, 1]
    |> assertOk
  let bv2 ←
    mkOp Kind.BITVECTOR_EXTRACT #[31, 2]
    |> assertOk
  assertEq bv1 bv1'
  assertNe bv1 bv2

test! do
  let x ← mkOp Kind.BITVECTOR_EXTRACT #[31, 1] |> assertOk
  assertEq x.getKind Kind.BITVECTOR_EXTRACT

test! do
  let x := Op.null ()
  assertEq x.isNull true
  let y ← mkOp Kind.BITVECTOR_EXTRACT #[31, 1] |> assertOk
  assertEq y.isNull false
  assertNe x y

test! do
  mkOp Kind.ADD
  |> assertOkDiscard
  mkOp Kind.BITVECTOR_EXTRACT
  |> assertError
    "invalid number of indices for operator BITVECTOR_EXTRACT, expected 2 but got 0."

test! do
  -- operators with 0 indices
  let plus ← mkOp Kind.ADD |> assertOk

  assertEq 0 plus.getNumIndices

  -- operators with 1 index
  let divisible ← mkOp Kind.DIVISIBLE #[4]
  let bvRepeat ← mkOp Kind.BITVECTOR_REPEAT #[5]
  let bvZeroExtend ← mkOp Kind.BITVECTOR_ZERO_EXTEND #[6]
  let bvSignExtend ← mkOp Kind.BITVECTOR_SIGN_EXTEND #[7]
  let bvRotateLeft ← mkOp Kind.BITVECTOR_ROTATE_LEFT #[8]
  let bvRotateRight ← mkOp Kind.BITVECTOR_ROTATE_RIGHT #[9]
  let intToBv ← mkOp Kind.INT_TO_BITVECTOR #[10]
  let iand ← mkOp Kind.IAND #[11]
  let fpToUbv ← mkOp Kind.FLOATINGPOINT_TO_UBV #[12]
  let fpToSbv ← mkOp Kind.FLOATINGPOINT_TO_SBV #[13]

  assertEq 1 divisible.getNumIndices
  assertEq 1 bvRepeat.getNumIndices
  assertEq 1 bvZeroExtend.getNumIndices
  assertEq 1 bvSignExtend.getNumIndices
  assertEq 1 bvRotateLeft.getNumIndices
  assertEq 1 bvRotateRight.getNumIndices
  assertEq 1 intToBv.getNumIndices
  assertEq 1 iand.getNumIndices
  assertEq 1 fpToUbv.getNumIndices
  assertEq 1 fpToSbv.getNumIndices

  -- operators with 2 indices
  let bvExtract ← mkOp Kind.BITVECTOR_EXTRACT #[1, 0]
  let toFpFromIeeeBv ← mkOp Kind.FLOATINGPOINT_TO_FP_FROM_IEEE_BV #[3, 2]
  let toFpFromFp ← mkOp Kind.FLOATINGPOINT_TO_FP_FROM_FP #[5, 4]
  let toFpFromReal ← mkOp Kind.FLOATINGPOINT_TO_FP_FROM_REAL #[7, 6]
  let toFpFromSbv ← mkOp Kind.FLOATINGPOINT_TO_FP_FROM_SBV #[9, 8]
  let toFpFromUbv ← mkOp Kind.FLOATINGPOINT_TO_FP_FROM_UBV #[11, 10]
  let regexpLoop ← mkOp Kind.REGEXP_LOOP #[15, 14]

  assertEq 2 bvExtract.getNumIndices
  assertEq 2 toFpFromIeeeBv.getNumIndices
  assertEq 2 toFpFromFp.getNumIndices
  assertEq 2 toFpFromReal.getNumIndices
  assertEq 2 toFpFromSbv.getNumIndices
  assertEq 2 toFpFromUbv.getNumIndices
  assertEq 2 regexpLoop.getNumIndices

  -- operators with n indices
  let indices := #[0, 3, 2, 0, 1, 2];
  let tupleProject ← mkOp Kind.TUPLE_PROJECT indices;
  assertEq indices.size tupleProject.getNumIndices

  let relationProject ← mkOp Kind.RELATION_PROJECT indices
  assertEq indices.size relationProject.getNumIndices

  let tableProject ← mkOp Kind.TABLE_PROJECT indices
  assertEq indices.size tableProject.getNumIndices

test! do
  -- operators with 0 indices
  let plus ← mkOp Kind.ADD |> assertOk

  -- can't test that `plus[0]` fails as there are no legal indices at lean-level
  assertEq plus.isIndexed false
  assertEq plus.getNumIndices 0

  -- helper for 1/n-indexed operators
  let check (op : Op) (idx : Nat) (intValue : Int) : cvc5.Env Unit :=
    if _ : idx < op.getNumIndices then
      assertEq op[idx].getIntegerValue! intValue
    else fail "illegal op index `{idx}` for {op}"

  -- operators with 1 index
  let divisible ← mkOp Kind.DIVISIBLE #[4]
  let bvRepeat ← mkOp Kind.BITVECTOR_REPEAT #[5]
  let bvZeroExtend ← mkOp Kind.BITVECTOR_ZERO_EXTEND #[6]
  let bvSignExtend ← mkOp Kind.BITVECTOR_SIGN_EXTEND #[7]
  let bvRotateLeft ← mkOp Kind.BITVECTOR_ROTATE_LEFT #[8]
  let bvRotateRight ← mkOp Kind.BITVECTOR_ROTATE_RIGHT #[9]
  let intToBv ← mkOp Kind.INT_TO_BITVECTOR #[10]
  let iand ← mkOp Kind.IAND #[11]
  let fpToUbv ← mkOp Kind.FLOATINGPOINT_TO_UBV #[12]
  let fpToSbv ← mkOp Kind.FLOATINGPOINT_TO_SBV #[13]

  check divisible 0 4
  check bvRepeat 0 5
  check bvZeroExtend 0 6
  check bvSignExtend 0 7
  check bvRotateLeft 0 8
  check bvRotateRight 0 9
  check intToBv 0 10
  check iand 0 11
  check fpToUbv 0 12
  check fpToSbv 0 13

  -- operators with 2 indices
  let bvExtract ← mkOp Kind.BITVECTOR_EXTRACT #[1, 0]
  let toFpFromIeeeBv ← mkOp Kind.FLOATINGPOINT_TO_FP_FROM_IEEE_BV #[3, 2]
  let toFpFromFp ← mkOp Kind.FLOATINGPOINT_TO_FP_FROM_FP #[5, 4]
  let toFpFromReal ← mkOp Kind.FLOATINGPOINT_TO_FP_FROM_REAL #[7, 6]
  let toFpFromSbv ← mkOp Kind.FLOATINGPOINT_TO_FP_FROM_SBV #[9, 8]
  let toFpFromUbv ← mkOp Kind.FLOATINGPOINT_TO_FP_FROM_UBV #[11, 10]
  let regexpLoop ← mkOp Kind.REGEXP_LOOP #[15, 14]

  check bvExtract 0 1
  check bvExtract 1 0
  check toFpFromIeeeBv 0 3
  check toFpFromIeeeBv 1 2
  check toFpFromFp 0 5
  check toFpFromFp 1 4
  check toFpFromReal 0 7
  check toFpFromReal 1 6
  check toFpFromSbv 0 9
  check toFpFromSbv 1 8
  check toFpFromUbv 0 11
  check toFpFromUbv 1 10
  check regexpLoop 0 15
  check regexpLoop 1 14

  -- operators with n indices
  let indices := #[0, 3, 2, 0, 1, 2];
  let tupleProject ← mkOp Kind.TUPLE_PROJECT indices;
  for idx in [0 : indices.size] do
    check tupleProject idx indices[idx]!

/-
Not sure what to do for the end of the test below. Original test is

```cpp
Op bitvector_repeat_ot = d_mkOp(Kind::BITVECTOR_REPEAT, {5});
std::string op_repr = bitvector_repeat_ot.toString();
ASSERT_EQ(bitvector_repeat_ot.toString(), op_repr);
{
  std::stringstream ss;
  ss << bitvector_repeat_ot;
  ASSERT_EQ(ss.str(), op_repr);
}
```

I don't know what test would make sense at lean-level for this last block, so it's ignored. The only
check left is not very interesting though.
-/
test! do
  let bitvectorRepeatOt ← mkOp Kind.BITVECTOR_REPEAT #[5]
  let opRepr := bitvectorRepeatOt.toString
  assertEq bitvectorRepeatOt.toString opRepr
  -- not sure what to do here, see comment above
