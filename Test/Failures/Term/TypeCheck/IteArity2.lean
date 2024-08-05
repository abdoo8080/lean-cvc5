import Test.Init

namespace cvc5.Test

def mkTerms : IO Unit := do
  let tm ← Term.Manager.mk

  let ite1 :=
    tm.mkTerm Kind.ITE #[tm.mkBoolean true, tm.mkInteger 7, tm.mkInteger 3, tm.mkInteger 11]
  assertEq ite1.getKind Kind.ITE "ite1.getKind"
  assertEq ite1.getSort.toString "Int" "ite1.getSort"

#eval mkTerms
