import Test.Init

namespace cvc5.Test

def mkTerms : IO Unit := do
  let tm ← Term.Manager.mk

  let boolKind := Kind.CONST_BOOLEAN

  let (tru, fls) := (
    tm.mkBoolean true,
    tm.mkBoolean false,
  )
  assertEq tru.getKind boolKind "tru.getKind"
  assertEq tru.getSort.toString "Bool" "tru.getSort"
  assertEq fls.getKind boolKind "fls.getKind"
  assertEq fls.getSort.toString "Bool" "fls.getSort"

  let intKind := Kind.CONST_INTEGER

  let (one, three, seven, eleven) := (
    tm.mkInteger 1,
    tm.mkInteger 3,
    tm.mkInteger 7,
    tm.mkInteger 11,
  )
  assertEq one.getKind intKind "one.getKind"
  assertEq one.getSort.toString "Int" "one.getSort"
  assertEq three.getKind intKind "three.getKind"
  assertEq three.getSort.toString "Int" "three.getSort"
  assertEq seven.getKind intKind "seven.getKind"
  assertEq seven.getSort.toString "Int" "seven.getSort"
  assertEq eleven.getKind intKind "eleven.getKind"
  assertEq eleven.getSort.toString "Int" "eleven.getSort"

  let ite1 :=
    tm.mkTerm Kind.ITE #[fls, three, seven]
  assertEq ite1.getKind Kind.ITE "ite1.getKind"
  assertEq ite1.getSort.toString "Int" "ite1.getSort"

  let eq1 :=
    tm.mkTerm Kind.EQUAL #[ite1, eleven]
  assertEq eq1.getKind Kind.EQUAL "eq1.getKind"
  assertEq eq1.getSort.toString "Bool" "eq1.getSort"

  let eq1' :=
    tm.mkTerm Kind.EQUAL #[ite1, eleven, one]
  assertEq eq1'.getKind Kind.AND "eq1'.getKind"
  assertEq eq1'.getSort.toString "Bool" "eq1'.getSort"

  let ite2 :=
    tm.mkTerm Kind.ITE #[tru, eq1, fls]
  assertEq ite2.getKind Kind.ITE "ite2.getKind"
  assertEq ite2.getSort.toString "Bool" "ite2.getSort"

#eval mkTerms
