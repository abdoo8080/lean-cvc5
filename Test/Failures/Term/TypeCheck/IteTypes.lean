import Test.Init

namespace cvc5.Test

def mkTerms : IO Unit := do
  let tm ← TermManager.new

  let ite1 :=
    tm.mkTerm Kind.ITE #[tm.mkBoolean true, tm.mkInteger 7, tm.mkBoolean false]
  assertEq ite1.getKind Kind.ITE "ite1.getKind"
  assertEq ite1.getSort.toString "Int" "ite1.getSort"

#eval mkTerms