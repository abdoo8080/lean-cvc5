import cvc5Test.Init

namespace cvc5.Test

def mkTerms1 : IO Unit := cvc5.runIO do
  let boolKind : Kind := cvc5.Kind.CONST_BOOLEAN

  let (tru, fls) := (
    ← Term.mkBoolean true,
    ← Term.mkBoolean false,
  )
  assertEq tru.getKind boolKind
  assertEq tru.getSort.toString "Bool"
  assertEq fls.getKind boolKind
  assertEq fls.getSort.toString "Bool"

  let intKind := Kind.CONST_INTEGER

  let (one, three, seven, eleven) := (
    ← Term.mkInteger 1,
    ← Term.mkInteger 3,
    ← Term.mkInteger 7,
    ← Term.mkInteger 11,
  )
  assertEq one.getKind intKind
  assertEq one.getSort.toString "Int"
  assertEq three.getKind intKind
  assertEq three.getSort.toString "Int"
  assertEq seven.getKind intKind
  assertEq seven.getSort.toString "Int"
  assertEq eleven.getKind intKind
  assertEq eleven.getSort.toString "Int"

  let ite1 ← Term.mk Kind.ITE #[fls, three, seven]
  assertEq ite1.getKind Kind.ITE
  assertEq ite1.getSort.toString "Int"

  let eq1 ← Term.mk Kind.EQUAL #[ite1, eleven]
  assertEq eq1.getKind Kind.EQUAL
  assertEq eq1.getSort.toString "Bool"

  let eq1' ← Term.mk Kind.EQUAL #[ite1, eleven, one]
  assertEq eq1'.getKind Kind.AND
  assertEq eq1'.getSort.toString "Bool"

  let ite2 ← Term.mk Kind.ITE #[tru, eq1, fls]
  assertEq ite2.getKind Kind.ITE
  assertEq ite2.getSort.toString "Bool"

#guard_msgs in
  #eval mkTerms1
