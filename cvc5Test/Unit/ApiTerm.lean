import cvc5Test.Init

/-! # Black box testing of the term manager

- <https://github.com/cvc5/cvc5/blob/e342ecb325520619db2a1f49e95f96ebca8029f2/test/unit/api/cpp/api_term_manager_black.cpp>
-/
namespace cvc5.Test

test![TestApiBlackTerm, equalHash] tm => do
  let uSort ← tm.mkUninterpretedSort "u"
  let x ← tm.mkVar uSort "x"
  let y ← tm.mkVar uSort "y"
  let z := Term.null ()

  assertTrue (x == x)
  assertFalse (x != x)
  assertFalse (x == y)
  assertTrue (x != y)
  assertFalse (x == z)
  assertTrue (x != z)

  assertEq x.hash x.hash
  assertNe x.hash y.hash
  assertEq 0 (Term.null ()).hash

test![TestApiBlackTerm, getId] tm => do
  let n := Term.null ()
  n.getId |> assertError
    "invalid call to 'uint64_t cvc5::Term::getId() const', expected non-null object"
  let x ← tm.mkVar (← tm.getIntegerSort) "x"
  x.getId |> assertOkDiscard
  let y := x
  assertEq (← x.getId) (← y.getId)

test![TestApiBlackTerm, getKind] tm => do
  let uSort ← tm.mkUninterpretedSort "u"
  let intSort ← tm.getIntegerSort
  let boolSort ← tm.getBooleanSort
  let funSort1 ← tm.mkFunctionSort #[uSort] intSort
  let funSort2 ← tm.mkFunctionSort #[intSort] boolSort

  let n := Term.null ()
  n.getKind |> assertError
    "invalid call to 'Kind cvc5::Term::getKind() const', expected non-null object"
  let x ← tm.mkVar uSort "x"
  x.getKind |> assertOkDiscard
  let y ← tm.mkVar uSort "y"
  y.getKind |> assertOkDiscard

  let f ← tm.mkVar funSort1 "f"
  f.getKind |> assertOkDiscard
  let p ← tm.mkVar funSort2 "p"
  p.getKind |> assertOkDiscard

  let zero ← tm.mkInteger 0
  zero.getKind |> assertOkDiscard

  let f_x ← tm.mkTerm Kind.APPLY_UF #[f, x]
  f_x.getKind |> assertOkDiscard
  let f_y ← tm.mkTerm Kind.APPLY_UF #[f, y]
  f_y.getKind |> assertOkDiscard
  let sum ← tm.mkTerm Kind.ADD #[f_x, f_y]
  sum.getKind |> assertOkDiscard
  let p_0 ← tm.mkTerm Kind.APPLY_UF #[p, zero]
  p_0.getKind |> assertOkDiscard
  let p_f_y ← tm.mkTerm Kind.APPLY_UF #[p, f_y]
  p_f_y.getKind |> assertOkDiscard

  let seqSort ← tm.mkSequenceSort intSort
  let s ← tm.mkConst seqSort "s"
  let ss ← tm.mkTerm Kind.SEQ_CONCAT #[s, s]
  assertEq Kind.SEQ_CONCAT (← ss.getKind)

test![TestApiBlackTerm, getSort] tm => do
  let bvSort ← tm.mkBitVectorSort 8
  let intSort ← tm.getIntegerSort
  let boolSort ← tm.getBooleanSort
  let funSort1 ← tm.mkFunctionSort #[bvSort] intSort
  let funSort2 ← tm.mkFunctionSort #[intSort] boolSort

  let n := Term.null ()
  n.getSort |> assertError
    "invalid call to 'Sort cvc5::Term::getSort() const', expected non-null object"
  let x ← tm.mkVar bvSort "x"
  x.getSort |> assertOkDiscard
  assertEq bvSort (← x.getSort)
  let y ← tm.mkVar bvSort "y"
  y.getSort |> assertOkDiscard
  assertEq bvSort (← y.getSort)

  let f ← tm.mkVar funSort1 "f"
  f.getSort |> assertOkDiscard
  assertEq funSort1 (← f.getSort)
  let p ← tm.mkVar funSort2 "p"
  p.getSort |> assertOkDiscard
  assertEq funSort2 (← p.getSort)

  let zero ← tm.mkInteger 0
  zero.getSort |> assertOkDiscard
  assertEq intSort (← zero.getSort)

  let f_x ← tm.mkTerm Kind.APPLY_UF #[f, x]
  f_x.getSort |> assertOkDiscard
  assertEq intSort (← f_x.getSort)
  let f_y ← tm.mkTerm Kind.APPLY_UF #[f, y]
  f_y.getSort |> assertOkDiscard
  assertEq intSort (← f_y.getSort)
  let sum ← tm.mkTerm Kind.ADD #[f_x, f_y]
  sum.getSort |> assertOkDiscard
  assertEq intSort (← sum.getSort)
  let p_0 ← tm.mkTerm Kind.APPLY_UF #[p, zero]
  p_0.getSort |> assertOkDiscard
  assertEq boolSort (← p_0.getSort)
  let p_f_y ← tm.mkTerm Kind.APPLY_UF #[p, f_y]
  p_f_y.getSort |> assertOkDiscard
  assertEq boolSort (← p_f_y.getSort)

test![TestApiBlackTerm, getOp] tm => do
  let intSort ← tm.getIntegerSort
  let bvSort ← tm.mkBitVectorSort 8
  let arrSort ← tm.mkArraySort bvSort intSort
  let funSort ← tm.mkFunctionSort #[intSort] bvSort

  let x ← tm.mkConst intSort "x"
  let a ← tm.mkConst arrSort "a"
  let b ← tm.mkConst bvSort "b"

  assertFalse x.hasOp
  x.getOp |> assertError "expected Term to have an Op when calling getOp()"

  let ab ← tm.mkTerm Kind.SELECT #[a, b]
  let ext ← tm.mkOp Kind.BITVECTOR_EXTRACT #[4, 0]
  let extb ← tm.mkTermOfOp ext #[b]

  assertTrue ab.hasOp
  assertFalse ab.getOp!.isIndexed
  -- can compare directly to a `Kind` (will invoke `Op` constructor)
  assertTrue extb.hasOp
  assertTrue extb.getOp!.isIndexed
  assertEq extb.getOp! ext

  let bit ← tm.mkOp Kind.BITVECTOR_BIT #[4]
  let bitb ← tm.mkTermOfOp bit #[b]
  assertEq Kind.BITVECTOR_BIT bitb.getKind!
  assertTrue bitb.hasOp
  assertEq bit bitb.getOp!
  assertTrue bitb.getOp!.isIndexed
  assertEq bit.getNumIndices 1
  assertEq (← tm.mkInteger 4) bit[0]!

  let f ← tm.mkConst funSort "f"
  let fx ← tm.mkTerm Kind.APPLY_UF #[f, x]

  assertFalse f.hasOp
  f.getOp |> assertError "expected Term to have an Op when calling getOp()"
  assertTrue fx.hasOp
  let children := fx.getChildren
  -- testing rebuild from op and children
  assertEq fx (← tm.mkTermOfOp fx.getOp! children)

  -- test datatype ops
  let sort ← tm.mkParamSort "T"
  let mut listDecl ← tm.mkDatatypeDecl "paramList" #[sort]
  let mut cons ← tm.mkDatatypeConstructorDecl "cons"
  let mut nil ← tm.mkDatatypeConstructorDecl "nil"
  cons ← cons.addSelector "head" sort
  cons ← cons.addSelectorSelf "tail"
  listDecl ← listDecl.addConstructor cons
  listDecl ← listDecl.addConstructor nil
  let listSort ← tm.mkDatatypeSort listDecl
  let intListSort ← listSort.instantiate #[← tm.getIntegerSort]
  let c ← tm.mkConst intListSort "c"
  let list ← listSort.getDatatype
  -- list datatype constructor and selector operator terms
  let consOpTerm ← (← list.getConstructor "cons").getTerm
  let nilOpTerm ← (← list.getConstructor "nil").getTerm
  let headOpTerm ← do
    let cs ← list.getConstructor "cons"
    let hd ← cs.getSelector "head"
    hd.getTerm
  let tailOpTerm ← do
    let cs ← list.getConstructor "cons"
    let hd ← cs.getSelector "tail"
    hd.getTerm

  let nilTerm ← tm.mkTerm Kind.APPLY_CONSTRUCTOR #[nilOpTerm]
  let consTerm ← tm.mkTerm Kind.APPLY_CONSTRUCTOR #[consOpTerm, ← tm.mkInteger 0, nilTerm]
  let headTerm ← tm.mkTerm Kind.APPLY_SELECTOR #[headOpTerm, consTerm]
  let tailTerm ← tm.mkTerm Kind.APPLY_SELECTOR #[tailOpTerm, consTerm]

  assertFalse c.hasOp
  assertTrue nilTerm.hasOp
  assertTrue consTerm.hasOp
  assertTrue headTerm.hasOp
  assertTrue tailTerm.hasOp

  -- test rebuilding
  let children := headTerm.getChildren
  assertEq headTerm (← tm.mkTermOfOp headTerm.getOp! children)

test![TestApiBlackTerm, hasGetSymbol] tm => do
  let n := Term.null ()
  let t ← tm.mkBoolean true
  let c ← tm.mkConst (← tm.getBooleanSort) "|\\|"

  n.hasSymbol |> assertError
    "invalid call to 'bool cvc5::Term::hasSymbol() const', expected non-null object"
  assertFalse (← t.hasSymbol)
  assertTrue (← c.hasSymbol)

  n.getSymbol |> assertError
    "invalid call to 'std::string cvc5::Term::getSymbol() const', expected non-null object"
  t.getSymbol |> assertError
    "invalid call to 'std::string cvc5::Term::getSymbol() const', \
    expected the term to have a symbol."
  assertEq "|\\|" (← c.getSymbol)

test![TestApiBlackTerm, isNull] tm => do
  let mut x := Term.null ()
  assertTrue x.isNull
  x ← tm.mkVar (← tm.mkBitVectorSort 4) "x"
  assertFalse x.isNull

test![TestApiBlackTerm, notTerm] tm => do
  let bvSort ← tm.mkBitVectorSort 8
  let intSort ← tm.getIntegerSort
  let boolSort ← tm.getBooleanSort
  let funSort1 ← tm.mkFunctionSort #[bvSort] intSort
  let funSort2 ← tm.mkFunctionSort #[intSort] boolSort

  Term.null () |>.notTerm |> assertError
    "invalid call to 'Term cvc5::Term::notTerm() const', expected non-null object"
  let b ← tm.mkTrue
  b.notTerm |> assertOkDiscard
  let x ← tm.mkVar (← tm.mkBitVectorSort 8) "x"
  x.notTerm |> assertError "expecting a Boolean subexpression"
  let f ← tm.mkVar funSort1 "f"
  f.notTerm |> assertError "expecting a Boolean subexpression"
  let p ← tm.mkVar funSort2 "p"
  p.notTerm |> assertError "expecting a Boolean subexpression"
  let zero ← tm.mkInteger 0
  zero.notTerm |> assertError "expecting a Boolean subexpression"
  let f_x ← tm.mkTerm Kind.APPLY_UF #[f, x]
  f_x.notTerm |> assertError "expecting a Boolean subexpression"
  let sum ← tm.mkTerm Kind.ADD #[f_x, f_x]
  sum.notTerm |> assertError "expecting a Boolean subexpression"
  let p_0 ← tm.mkTerm Kind.APPLY_UF #[p, zero]
  p_0.notTerm |> assertOkDiscard
  let p_f_x ← tm.mkTerm Kind.APPLY_UF #[p, f_x]
  p_f_x.notTerm |> assertOkDiscard

test![TestApiBlackTerm, andTerm] tm => do
  let bvSort ← tm.mkBitVectorSort 8
  let intSort ← tm.getIntegerSort
  let boolSort ← tm.getBooleanSort
  let funSort1 ← tm.mkFunctionSort #[bvSort] intSort
  let funSort2 ← tm.mkFunctionSort #[intSort] boolSort

  let n := Term.null ()
  let b ← tm.mkTrue
  n.andTerm b |> assertError
    "invalid call to 'Term cvc5::Term::andTerm(const Term &) const', expected non-null object"
  b.andTerm n |> assertError "invalid null argument for 't'"
  b.andTerm b |> assertOkDiscard
  let x ← tm.mkVar (← tm.mkBitVectorSort 8) "x"
  x.andTerm b |> assertError "expecting a Boolean subexpression"
  x.andTerm x |> assertError "expecting a Boolean subexpression"
  let f ← tm.mkVar funSort1 "f"
  f.andTerm b |> assertError "expecting a Boolean subexpression"
  f.andTerm x |> assertError "expecting a Boolean subexpression"
  f.andTerm f |> assertError "expecting a Boolean subexpression"
  let p ← tm.mkVar funSort2 "p"
  p.andTerm b |> assertError "expecting a Boolean subexpression"
  p.andTerm x |> assertError "expecting a Boolean subexpression"
  p.andTerm f |> assertError "expecting a Boolean subexpression"
  p.andTerm p |> assertError "expecting a Boolean subexpression"
  let zero ← tm.mkInteger 0
  zero.andTerm b |> assertError "expecting a Boolean subexpression"
  zero.andTerm x |> assertError "expecting a Boolean subexpression"
  zero.andTerm f |> assertError "expecting a Boolean subexpression"
  zero.andTerm p |> assertError "expecting a Boolean subexpression"
  zero.andTerm zero |> assertError "expecting a Boolean subexpression"
  let f_x ← tm.mkTerm Kind.APPLY_UF #[f, x]
  f_x.andTerm b |> assertError "expecting a Boolean subexpression"
  f_x.andTerm x |> assertError "expecting a Boolean subexpression"
  f_x.andTerm f |> assertError "expecting a Boolean subexpression"
  f_x.andTerm p |> assertError "expecting a Boolean subexpression"
  f_x.andTerm zero |> assertError "expecting a Boolean subexpression"
  f_x.andTerm f_x |> assertError "expecting a Boolean subexpression"
  let sum ← tm.mkTerm Kind.ADD #[f_x, f_x]
  sum.andTerm b |> assertError "expecting a Boolean subexpression"
  sum.andTerm x |> assertError "expecting a Boolean subexpression"
  sum.andTerm f |> assertError "expecting a Boolean subexpression"
  sum.andTerm p |> assertError "expecting a Boolean subexpression"
  sum.andTerm zero |> assertError "expecting a Boolean subexpression"
  sum.andTerm f_x |> assertError "expecting a Boolean subexpression"
  sum.andTerm sum |> assertError "expecting a Boolean subexpression"
  let p_0 ← tm.mkTerm Kind.APPLY_UF #[p, zero]
  p_0.andTerm b |> assertOkDiscard
  p_0.andTerm x |> assertError "expecting a Boolean subexpression"
  p_0.andTerm f |> assertError "expecting a Boolean subexpression"
  p_0.andTerm p |> assertError "expecting a Boolean subexpression"
  p_0.andTerm zero |> assertError "expecting a Boolean subexpression"
  p_0.andTerm f_x |> assertError "expecting a Boolean subexpression"
  p_0.andTerm sum |> assertError "expecting a Boolean subexpression"
  p_0.andTerm p_0 |> assertOkDiscard
  let p_f_x ← tm.mkTerm Kind.APPLY_UF #[p, f_x]
  p_f_x.andTerm b |> assertOkDiscard
  p_f_x.andTerm x |> assertError "expecting a Boolean subexpression"
  p_f_x.andTerm f |> assertError "expecting a Boolean subexpression"
  p_f_x.andTerm p |> assertError "expecting a Boolean subexpression"
  p_f_x.andTerm zero |> assertError "expecting a Boolean subexpression"
  p_f_x.andTerm f_x |> assertError "expecting a Boolean subexpression"
  p_f_x.andTerm sum |> assertError "expecting a Boolean subexpression"
  p_f_x.andTerm p_0 |> assertOkDiscard
  p_f_x.andTerm p_f_x |> assertOkDiscard

test![TestApiBlackTerm, orTerm] tm => do
  let bvSort ← tm.mkBitVectorSort 8
  let intSort ← tm.getIntegerSort
  let boolSort ← tm.getBooleanSort
  let funSort1 ← tm.mkFunctionSort #[bvSort] intSort
  let funSort2 ← tm.mkFunctionSort #[intSort] boolSort

  let n := Term.null ()
  let b ← tm.mkTrue
  n.orTerm b |> assertError
    "invalid call to 'Term cvc5::Term::orTerm(const Term &) const', expected non-null object"
  b.orTerm n |> assertError "invalid null argument for 't'"
  b.orTerm b |> assertOkDiscard
  let x ← tm.mkVar (← tm.mkBitVectorSort 8) "x"
  x.orTerm b |> assertError "expecting a Boolean subexpression"
  x.orTerm x |> assertError "expecting a Boolean subexpression"
  let f ← tm.mkVar funSort1 "f"
  f.orTerm b |> assertError "expecting a Boolean subexpression"
  f.orTerm x |> assertError "expecting a Boolean subexpression"
  f.orTerm f |> assertError "expecting a Boolean subexpression"
  let p ← tm.mkVar funSort2 "p"
  p.orTerm b |> assertError "expecting a Boolean subexpression"
  p.orTerm x |> assertError "expecting a Boolean subexpression"
  p.orTerm f |> assertError "expecting a Boolean subexpression"
  p.orTerm p |> assertError "expecting a Boolean subexpression"
  let zero ← tm.mkInteger 0
  zero.orTerm b |> assertError "expecting a Boolean subexpression"
  zero.orTerm x |> assertError "expecting a Boolean subexpression"
  zero.orTerm f |> assertError "expecting a Boolean subexpression"
  zero.orTerm p |> assertError "expecting a Boolean subexpression"
  zero.orTerm zero |> assertError "expecting a Boolean subexpression"
  let f_x ← tm.mkTerm Kind.APPLY_UF #[f, x]
  f_x.orTerm b |> assertError "expecting a Boolean subexpression"
  f_x.orTerm x |> assertError "expecting a Boolean subexpression"
  f_x.orTerm f |> assertError "expecting a Boolean subexpression"
  f_x.orTerm p |> assertError "expecting a Boolean subexpression"
  f_x.orTerm zero |> assertError "expecting a Boolean subexpression"
  f_x.orTerm f_x |> assertError "expecting a Boolean subexpression"
  let sum ← tm.mkTerm Kind.ADD #[f_x, f_x]
  sum.orTerm b |> assertError "expecting a Boolean subexpression"
  sum.orTerm x |> assertError "expecting a Boolean subexpression"
  sum.orTerm f |> assertError "expecting a Boolean subexpression"
  sum.orTerm p |> assertError "expecting a Boolean subexpression"
  sum.orTerm zero |> assertError "expecting a Boolean subexpression"
  sum.orTerm f_x |> assertError "expecting a Boolean subexpression"
  sum.orTerm sum |> assertError "expecting a Boolean subexpression"
  let p_0 ← tm.mkTerm Kind.APPLY_UF #[p, zero]
  p_0.orTerm b |> assertOkDiscard
  p_0.orTerm x |> assertError "expecting a Boolean subexpression"
  p_0.orTerm f |> assertError "expecting a Boolean subexpression"
  p_0.orTerm p |> assertError "expecting a Boolean subexpression"
  p_0.orTerm zero |> assertError "expecting a Boolean subexpression"
  p_0.orTerm f_x |> assertError "expecting a Boolean subexpression"
  p_0.orTerm sum |> assertError "expecting a Boolean subexpression"
  p_0.orTerm p_0 |> assertOkDiscard
  let p_f_x ← tm.mkTerm Kind.APPLY_UF #[p, f_x]
  p_f_x.orTerm b |> assertOkDiscard
  p_f_x.orTerm x |> assertError "expecting a Boolean subexpression"
  p_f_x.orTerm f |> assertError "expecting a Boolean subexpression"
  p_f_x.orTerm p |> assertError "expecting a Boolean subexpression"
  p_f_x.orTerm zero |> assertError "expecting a Boolean subexpression"
  p_f_x.orTerm f_x |> assertError "expecting a Boolean subexpression"
  p_f_x.orTerm sum |> assertError "expecting a Boolean subexpression"
  p_f_x.orTerm p_0 |> assertOkDiscard
  p_f_x.orTerm p_f_x |> assertOkDiscard

test![TestApiBlackTerm, xorTerm] tm => do
  let bvSort ← tm.mkBitVectorSort 8
  let intSort ← tm.getIntegerSort
  let boolSort ← tm.getBooleanSort
  let funSort1 ← tm.mkFunctionSort #[bvSort] intSort
  let funSort2 ← tm.mkFunctionSort #[intSort] boolSort

  let n := Term.null ()
  let b ← tm.mkTrue
  n.xorTerm b |> assertError
    "invalid call to 'Term cvc5::Term::xorTerm(const Term &) const', expected non-null object"
  b.xorTerm n |> assertError "invalid null argument for 't'"
  b.xorTerm b |> assertOkDiscard
  let x ← tm.mkVar (← tm.mkBitVectorSort 8) "x"
  x.xorTerm b |> assertError "expecting a Boolean subexpression"
  x.xorTerm x |> assertError "expecting a Boolean subexpression"
  let f ← tm.mkVar funSort1 "f"
  f.xorTerm b |> assertError "expecting a Boolean subexpression"
  f.xorTerm x |> assertError "expecting a Boolean subexpression"
  f.xorTerm f |> assertError "expecting a Boolean subexpression"
  let p ← tm.mkVar funSort2 "p"
  p.xorTerm b |> assertError "expecting a Boolean subexpression"
  p.xorTerm x |> assertError "expecting a Boolean subexpression"
  p.xorTerm f |> assertError "expecting a Boolean subexpression"
  p.xorTerm p |> assertError "expecting a Boolean subexpression"
  let zero ← tm.mkInteger 0
  zero.xorTerm b |> assertError "expecting a Boolean subexpression"
  zero.xorTerm x |> assertError "expecting a Boolean subexpression"
  zero.xorTerm f |> assertError "expecting a Boolean subexpression"
  zero.xorTerm p |> assertError "expecting a Boolean subexpression"
  zero.xorTerm zero |> assertError "expecting a Boolean subexpression"
  let f_x ← tm.mkTerm Kind.APPLY_UF #[f, x]
  f_x.xorTerm b |> assertError "expecting a Boolean subexpression"
  f_x.xorTerm x |> assertError "expecting a Boolean subexpression"
  f_x.xorTerm f |> assertError "expecting a Boolean subexpression"
  f_x.xorTerm p |> assertError "expecting a Boolean subexpression"
  f_x.xorTerm zero |> assertError "expecting a Boolean subexpression"
  f_x.xorTerm f_x |> assertError "expecting a Boolean subexpression"
  let sum ← tm.mkTerm Kind.ADD #[f_x, f_x]
  sum.xorTerm b |> assertError "expecting a Boolean subexpression"
  sum.xorTerm x |> assertError "expecting a Boolean subexpression"
  sum.xorTerm f |> assertError "expecting a Boolean subexpression"
  sum.xorTerm p |> assertError "expecting a Boolean subexpression"
  sum.xorTerm zero |> assertError "expecting a Boolean subexpression"
  sum.xorTerm f_x |> assertError "expecting a Boolean subexpression"
  sum.xorTerm sum |> assertError "expecting a Boolean subexpression"
  let p_0 ← tm.mkTerm Kind.APPLY_UF #[p, zero]
  p_0.xorTerm b |> assertOkDiscard
  p_0.xorTerm x |> assertError "expecting a Boolean subexpression"
  p_0.xorTerm f |> assertError "expecting a Boolean subexpression"
  p_0.xorTerm p |> assertError "expecting a Boolean subexpression"
  p_0.xorTerm zero |> assertError "expecting a Boolean subexpression"
  p_0.xorTerm f_x |> assertError "expecting a Boolean subexpression"
  p_0.xorTerm sum |> assertError "expecting a Boolean subexpression"
  p_0.xorTerm p_0 |> assertOkDiscard
  let p_f_x ← tm.mkTerm Kind.APPLY_UF #[p, f_x]
  p_f_x.xorTerm b |> assertOkDiscard
  p_f_x.xorTerm x |> assertError "expecting a Boolean subexpression"
  p_f_x.xorTerm f |> assertError "expecting a Boolean subexpression"
  p_f_x.xorTerm p |> assertError "expecting a Boolean subexpression"
  p_f_x.xorTerm zero |> assertError "expecting a Boolean subexpression"
  p_f_x.xorTerm f_x |> assertError "expecting a Boolean subexpression"
  p_f_x.xorTerm sum |> assertError "expecting a Boolean subexpression"
  p_f_x.xorTerm p_0 |> assertOkDiscard
  p_f_x.xorTerm p_f_x |> assertOkDiscard

test![TestApiBlackTerm, eqTerm] tm => do
  let bvSort ← tm.mkBitVectorSort 8
  let intSort ← tm.getIntegerSort
  let boolSort ← tm.getBooleanSort
  let funSort1 ← tm.mkFunctionSort #[bvSort] intSort
  let funSort2 ← tm.mkFunctionSort #[intSort] boolSort

  let n := Term.null ()
  let b ← tm.mkTrue
  n.eqTerm b |> assertError
    "invalid call to 'Term cvc5::Term::eqTerm(const Term &) const', expected non-null object"
  b.eqTerm n |> assertError "invalid null argument for 't'"
  b.eqTerm b |> assertOkDiscard
  let x ← tm.mkVar (← tm.mkBitVectorSort 8) "x"
  x.eqTerm b |> assertError
    "Subexpressions must have the same type:\n\
    Equation: (= x true)\nType 1: (_ BitVec 8)\nType 2: Bool\n"
  x.eqTerm x |> assertOkDiscard
  let f ← tm.mkVar funSort1 "f"
  f.eqTerm b |> assertError
    "Subexpressions must have the same type:\n\
    Equation: (= f true)\nType 1: (-> (_ BitVec 8) Int)\nType 2: Bool\n"
  f.eqTerm x |> assertError
    "Subexpressions must have the same type:\n\
    Equation: (= f x)\nType 1: (-> (_ BitVec 8) Int)\nType 2: (_ BitVec 8)\n"
  f.eqTerm f |> assertOkDiscard
  let p ← tm.mkVar funSort2 "p"
  p.eqTerm b |> assertError
    "Subexpressions must have the same type:\n\
    Equation: (= p true)\nType 1: (-> Int Bool)\nType 2: Bool\n"
  p.eqTerm x |> assertError
    "Subexpressions must have the same type:\n\
    Equation: (= p x)\nType 1: (-> Int Bool)\nType 2: (_ BitVec 8)\n"
  p.eqTerm f |> assertError
    "Subexpressions must have the same type:\n\
    Equation: (= p f)\nType 1: (-> Int Bool)\nType 2: (-> (_ BitVec 8) Int)\n"
  p.eqTerm p |> assertOkDiscard
  let zero ← tm.mkInteger 0
  zero.eqTerm b |> assertError
    "Subexpressions must have the same type:\n\
    Equation: (= 0 true)\nType 1: Int\nType 2: Bool\n"
  zero.eqTerm x |> assertError
    "Subexpressions must have the same type:\n\
    Equation: (= 0 x)\nType 1: Int\nType 2: (_ BitVec 8)\n"
  zero.eqTerm f |> assertError
    "Subexpressions must have the same type:\n\
    Equation: (= 0 f)\nType 1: Int\nType 2: (-> (_ BitVec 8) Int)\n"
  zero.eqTerm p |> assertError
    "Subexpressions must have the same type:\n\
    Equation: (= 0 p)\nType 1: Int\nType 2: (-> Int Bool)\n"
  zero.eqTerm zero |> assertOkDiscard
  let f_x ← tm.mkTerm Kind.APPLY_UF #[f, x]
  f_x.eqTerm b |> assertError
    "Subexpressions must have the same type:\n\
    Equation: (= (f x) true)\nType 1: Int\nType 2: Bool"
  f_x.eqTerm x |> assertError
    "Subexpressions must have the same type:\n\
    Equation: (= (f x) x)\nType 1: Int\nType 2: (_ BitVec 8)\n"
  f_x.eqTerm f |> assertError
    "Subexpressions must have the same type:\n\
    Equation: (= (f x) f)\nType 1: Int\nType 2: (-> (_ BitVec 8) Int)\n"
  f_x.eqTerm p |> assertError
    "Subexpressions must have the same type:\n\
    Equation: (= (f x) p)\nType 1: Int\nType 2: (-> Int Bool)\n"
  f_x.eqTerm zero |> assertOkDiscard
  f_x.eqTerm f_x |> assertOkDiscard
  let sum ← tm.mkTerm Kind.ADD #[f_x, f_x]
  sum.eqTerm b |> assertError
    "Subexpressions must have the same type:\n\
    Equation: (let ((_let_1 (f x))) (= (+ _let_1 _let_1) true))\nType 1: Int\nType 2: Bool\n"
  sum.eqTerm x |> assertError
    "Subexpressions must have the same type:\n\
    Equation: (let ((_let_1 (f x))) (= (+ _let_1 _let_1) x))\nType 1: Int\nType 2: (_ BitVec 8)\n"
  sum.eqTerm f |> assertError
    "Subexpressions must have the same type:\n\
    Equation: (let ((_let_1 (f x))) (= (+ _let_1 _let_1) f))\nType 1: Int\n\
    Type 2: (-> (_ BitVec 8) Int)\n"
  sum.eqTerm p |> assertError
    "Subexpressions must have the same type:\n\
    Equation: (let ((_let_1 (f x))) (= (+ _let_1 _let_1) p))\nType 1: Int\nType 2: (-> Int Bool)\n"
  sum.eqTerm zero |> assertOkDiscard
  sum.eqTerm f_x |> assertOkDiscard
  sum.eqTerm sum |> assertOkDiscard
  let p_0 ← tm.mkTerm Kind.APPLY_UF #[p, zero]
  p_0.eqTerm b |> assertOkDiscard
  p_0.eqTerm x |> assertError
    "Subexpressions must have the same type:\n\
    Equation: (= (p 0) x)\nType 1: Bool\nType 2: (_ BitVec 8)\n"
  p_0.eqTerm f |> assertError
    "Subexpressions must have the same type:\n\
    Equation: (= (p 0) f)\nType 1: Bool\nType 2: (-> (_ BitVec 8) Int)\n"
  p_0.eqTerm p |> assertError
    "Subexpressions must have the same type:\n\
    Equation: (= (p 0) p)\nType 1: Bool\nType 2: (-> Int Bool)\n"
  p_0.eqTerm zero |> assertError
    "Subexpressions must have the same type:\n\
    Equation: (= (p 0) 0)\nType 1: Bool\nType 2: Int\n"
  p_0.eqTerm f_x |> assertError
    "Subexpressions must have the same type:\n\
    Equation: (= (p 0) (f x))\nType 1: Bool\nType 2: Int\n"
  p_0.eqTerm sum |> assertError
    "Subexpressions must have the same type:\n\
    Equation: (let ((_let_1 (f x))) (= (p 0) (+ _let_1 _let_1)))\nType 1: Bool\nType 2: Int\n"
  p_0.eqTerm p_0 |> assertOkDiscard
  let p_f_x ← tm.mkTerm Kind.APPLY_UF #[p, f_x]
  p_f_x.eqTerm b |> assertOkDiscard
  p_f_x.eqTerm x |> assertError
    "Subexpressions must have the same type:\n\
    Equation: (= (p (f x)) x)\nType 1: Bool\nType 2: (_ BitVec 8)\n"
  p_f_x.eqTerm f |> assertError
    "Subexpressions must have the same type:\n\
    Equation: (= (p (f x)) f)\nType 1: Bool\nType 2: (-> (_ BitVec 8) Int)\n"
  p_f_x.eqTerm p |> assertError
    "Subexpressions must have the same type:\n\
    Equation: (= (p (f x)) p)\nType 1: Bool\nType 2: (-> Int Bool)\n"
  p_f_x.eqTerm zero |> assertError
    "Subexpressions must have the same type:\n\
    Equation: (= (p (f x)) 0)\nType 1: Bool\nType 2: Int\n"
  p_f_x.eqTerm f_x |> assertError
    "Subexpressions must have the same type:\n\
    Equation: (let ((_let_1 (f x))) (= (p _let_1) _let_1))\nType 1: Bool\nType 2: Int\n"
  p_f_x.eqTerm sum |> assertError
    "Subexpressions must have the same type:\n\
    Equation: (let ((_let_1 (f x))) (= (p _let_1) (+ _let_1 _let_1)))\nType 1: Bool\nType 2: Int\n"
  p_f_x.eqTerm p_0 |> assertOkDiscard
  p_f_x.eqTerm p_f_x |> assertOkDiscard

test![TestApiBlackTerm, impTerm] tm => do
  let bvSort ← tm.mkBitVectorSort 8
  let intSort ← tm.getIntegerSort
  let boolSort ← tm.getBooleanSort
  let funSort1 ← tm.mkFunctionSort #[bvSort] intSort
  let funSort2 ← tm.mkFunctionSort #[intSort] boolSort

  let n := Term.null ()
  let b ← tm.mkTrue
  n.impTerm b |> assertError
    "invalid call to 'Term cvc5::Term::impTerm(const Term &) const', expected non-null object"
  b.impTerm n |> assertError "invalid null argument for 't'"
  b.impTerm b |> assertOkDiscard
  let x ← tm.mkVar (← tm.mkBitVectorSort 8) "x"
  x.impTerm b |> assertError "expecting a Boolean subexpression"
  x.impTerm x |> assertError "expecting a Boolean subexpression"
  let f ← tm.mkVar funSort1 "f"
  f.impTerm b |> assertError "expecting a Boolean subexpression"
  f.impTerm x |> assertError "expecting a Boolean subexpression"
  f.impTerm f |> assertError "expecting a Boolean subexpression"
  let p ← tm.mkVar funSort2 "p"
  p.impTerm b |> assertError "expecting a Boolean subexpression"
  p.impTerm x |> assertError "expecting a Boolean subexpression"
  p.impTerm f |> assertError "expecting a Boolean subexpression"
  p.impTerm p |> assertError "expecting a Boolean subexpression"
  let zero ← tm.mkInteger 0
  zero.impTerm b |> assertError "expecting a Boolean subexpression"
  zero.impTerm x |> assertError "expecting a Boolean subexpression"
  zero.impTerm f |> assertError "expecting a Boolean subexpression"
  zero.impTerm p |> assertError "expecting a Boolean subexpression"
  zero.impTerm zero |> assertError "expecting a Boolean subexpression"
  let f_x ← tm.mkTerm Kind.APPLY_UF #[f, x]
  f_x.impTerm b |> assertError "expecting a Boolean subexpression"
  f_x.impTerm x |> assertError "expecting a Boolean subexpression"
  f_x.impTerm f |> assertError "expecting a Boolean subexpression"
  f_x.impTerm p |> assertError "expecting a Boolean subexpression"
  f_x.impTerm zero |> assertError "expecting a Boolean subexpression"
  f_x.impTerm f_x |> assertError "expecting a Boolean subexpression"
  let sum ← tm.mkTerm Kind.ADD #[f_x, f_x]
  sum.impTerm b |> assertError "expecting a Boolean subexpression"
  sum.impTerm x |> assertError "expecting a Boolean subexpression"
  sum.impTerm f |> assertError "expecting a Boolean subexpression"
  sum.impTerm p |> assertError "expecting a Boolean subexpression"
  sum.impTerm zero |> assertError "expecting a Boolean subexpression"
  sum.impTerm f_x |> assertError "expecting a Boolean subexpression"
  sum.impTerm sum |> assertError "expecting a Boolean subexpression"
  let p_0 ← tm.mkTerm Kind.APPLY_UF #[p, zero]
  p_0.impTerm b |> assertOkDiscard
  p_0.impTerm x |> assertError "expecting a Boolean subexpression"
  p_0.impTerm f |> assertError "expecting a Boolean subexpression"
  p_0.impTerm p |> assertError "expecting a Boolean subexpression"
  p_0.impTerm zero |> assertError "expecting a Boolean subexpression"
  p_0.impTerm f_x |> assertError "expecting a Boolean subexpression"
  p_0.impTerm sum |> assertError "expecting a Boolean subexpression"
  p_0.impTerm p_0 |> assertOkDiscard
  let p_f_x ← tm.mkTerm Kind.APPLY_UF #[p, f_x]
  p_f_x.impTerm b |> assertOkDiscard
  p_f_x.impTerm x |> assertError "expecting a Boolean subexpression"
  p_f_x.impTerm f |> assertError "expecting a Boolean subexpression"
  p_f_x.impTerm p |> assertError "expecting a Boolean subexpression"
  p_f_x.impTerm zero |> assertError "expecting a Boolean subexpression"
  p_f_x.impTerm f_x |> assertError "expecting a Boolean subexpression"
  p_f_x.impTerm sum |> assertError "expecting a Boolean subexpression"
  p_f_x.impTerm p_0 |> assertOkDiscard
  p_f_x.impTerm p_f_x |> assertOkDiscard

test![TestApiBlackTerm, iteTerm] tm => do
  let bvSort ← tm.mkBitVectorSort 8
  let intSort ← tm.getIntegerSort
  let boolSort ← tm.getBooleanSort
  let funSort1 ← tm.mkFunctionSort #[bvSort] intSort
  let funSort2 ← tm.mkFunctionSort #[intSort] boolSort

  let n := Term.null ()
  let b ← tm.mkTrue
  n.iteTerm b b |> assertError
    "invalid call to 'Term cvc5::Term::iteTerm(const Term &, const Term &) const', \
    expected non-null object"
  b.iteTerm n b |> assertError "invalid null argument for 'then_t'"
  b.iteTerm b n |> assertError "invalid null argument for 'else_t'"
  b.iteTerm b b |> assertOkDiscard
  let x ← tm.mkVar (← tm.mkBitVectorSort 8) "x"
  b.iteTerm x x |> assertOkDiscard
  b.iteTerm b b |> assertOkDiscard -- also tested twice in the original test
  b.iteTerm x b |> assertError
    "Branches of the ITE must have comparable type.\n\
    then branch: x\nits type   : (_ BitVec 8)\nelse branch: true\nits type   : Bool\n"
  x.iteTerm x x |> assertError "condition of ITE is not Boolean"
  x.iteTerm x b |> assertError
    "Branches of the ITE must have comparable type.\n\
    then branch: x\nits type   : (_ BitVec 8)\nelse branch: true\nits type   : Bool\n"
  let f ← tm.mkVar funSort1 "f"
  f.iteTerm b b |> assertError "condition of ITE is not Boolean"
  x.iteTerm b x |> assertError
    "Branches of the ITE must have comparable type.\n\
    then branch: true\nits type   : Bool\nelse branch: x\nits type   : (_ BitVec 8)\n"
  let p ← tm.mkVar funSort2 "p"
  p.iteTerm b b |> assertError "condition of ITE is not Boolean"
  p.iteTerm x b |> assertError
    "Branches of the ITE must have comparable type.\n\
    then branch: x\nits type   : (_ BitVec 8)\nelse branch: true\nits type   : Bool\n"
  let zero ← tm.mkInteger 0
  zero.iteTerm x x |> assertError "condition of ITE is not Boolean"
  zero.iteTerm x b |> assertError
    "Branches of the ITE must have comparable type.\n\
    then branch: x\nits type   : (_ BitVec 8)\nelse branch: true\nits type   : Bool\n"
  let f_x ← tm.mkTerm Kind.APPLY_UF #[f, x]
  f_x.iteTerm b b |> assertError "condition of ITE is not Boolean"
  f_x.iteTerm b x |> assertError
    "Branches of the ITE must have comparable type.\n\
    then branch: true\nits type   : Bool\nelse branch: x\nits type   : (_ BitVec 8)\n"
  let sum ← tm.mkTerm Kind.ADD #[f_x, f_x]
  sum.iteTerm x x |> assertError "condition of ITE is not Boolean"
  sum.iteTerm b x |> assertError
    "Branches of the ITE must have comparable type.\n\
    then branch: true\nits type   : Bool\nelse branch: x\nits type   : (_ BitVec 8)\n"
  let p_0 ← tm.mkTerm Kind.APPLY_UF #[p, zero]
  p_0.iteTerm b b |> assertOkDiscard
  p_0.iteTerm x x |> assertOkDiscard
  p_0.iteTerm x b |> assertError
    "Branches of the ITE must have comparable type.\n\
    then branch: x\nits type   : (_ BitVec 8)\nelse branch: true\nits type   : Bool\n"
  let p_f_x ← tm.mkTerm Kind.APPLY_UF #[p, f_x]
  p_f_x.iteTerm b b |> assertOkDiscard
  p_f_x.iteTerm x x |> assertOkDiscard
  p_f_x.iteTerm x b |> assertError
    "Branches of the ITE must have comparable type.\n\
    then branch: x\nits type   : (_ BitVec 8)\nelse branch: true\nits type   : Bool\n"

set_option linter.unusedVariables false in -- censoring the *unused variable* warning for `t2`
test![TestApiBlackTerm, termAssignment] tm => do
  let t1 ← tm.mkInteger 1
  let mut t2 := t1
  t2 ← tm.mkInteger 2
  assertEq t1 (← tm.mkInteger 1)

test![TestApiBlackTerm, termCompare] tm => do
  let t1 ← tm.mkInteger 1
  let t2 ← tm.mkTerm Kind.ADD #[← tm.mkInteger 2, ← tm.mkInteger 2]
  let t3 ← tm.mkTerm Kind.ADD #[← tm.mkInteger 2, ← tm.mkInteger 2]
  assertTrue (t2 ≥ t3)
  assertTrue (t2 ≤ t3)
  assertTrue <| (t1 > t2) != (t1 < t2)
  assertTrue <| (t1 > t2 || t1 == t2) == (t1 ≥ t2)

test![TestApiBlackTerm, termChildren] tm => do
  -- simple term `2+3`
  let two ← tm.mkInteger 2
  let t1 ← tm.mkTerm Kind.ADD #[two, ← tm.mkInteger 3]
  assertEq two t1[0]!
  assertEq 2 t1.getNumChildren
  let n := Term.null ()
  -- -- lean's version of `getNumChildren` produces `0` on `null` terms
  -- n.getNumChildren |> assertError
  --   "invalid call to 'size_t cvc5::Term::getNumChildren() const', expected non-null object"
  assertEq 0 n.getNumChildren

  for kid in t1 do assertTrue kid.isIntegerValue

  -- apply term `f(2)`
  let intSort ← tm.getIntegerSort
  let fSort ← tm.mkFunctionSort #[intSort] intSort
  let f ← tm.mkConst fSort "f"
  let t2 ← tm.mkTerm Kind.APPLY_UF #[f, two]
  -- due to our higher-order view of terms, we treat f as a child of `APPLY_UF`
  assertEq 2 t2.getNumChildren
  assertEq f t2[0]!
  assertEq two t2[1]!
  -- original test checks that `n[0]` fails, but that call is invalid in the lean API

test![TestApiBlackTerm, getInteger] tm => do
  let int1 ← tm.mkIntegerOfString "-18446744073709551616"
  let int2 ← tm.mkIntegerOfString "-18446744073709551615"
  let int3 ← tm.mkIntegerOfString "-4294967296"
  let int4 ← tm.mkIntegerOfString "-4294967295"
  let int5 ← tm.mkIntegerOfString "-10"
  let int6 ← tm.mkIntegerOfString "0"
  let int7 ← tm.mkIntegerOfString "10"
  let int8 ← tm.mkIntegerOfString "4294967295"
  let int9 ← tm.mkIntegerOfString "4294967296"
  let int10 ← tm.mkIntegerOfString "18446744073709551615"
  let int11 ← tm.mkIntegerOfString "18446744073709551616"
  let int12 ← tm.mkIntegerOfString "-0"

  tm.mkIntegerOfString "" |> assertError
    "invalid argument '' for 's', expected an integer "
  tm.mkIntegerOfString "-" |> assertError
    "invalid argument '-' for 's', expected an integer "
  tm.mkIntegerOfString "-1-" |> assertError
    "invalid argument '-1-' for 's', expected an integer "
  tm.mkIntegerOfString "0.0" |> assertError
    "invalid argument '0.0' for 's', expected an integer "
  tm.mkIntegerOfString "-0.1" |> assertError
    "invalid argument '-0.1' for 's', expected an integer "
  tm.mkIntegerOfString "012" |> assertError
    "invalid argument '012' for 's', expected an integer "
  tm.mkIntegerOfString "0000" |> assertError
    "invalid argument '0000' for 's', expected an integer "
  tm.mkIntegerOfString "-01" |> assertError
    "invalid argument '-01' for 's', expected an integer "
  tm.mkIntegerOfString "-00" |> assertError
    "invalid argument '-00' for 's', expected an integer "

  assertTrue (
    ¬ int1.isInt32Value ∧ ¬ int1.isUInt32Value ∧ ¬ int1.isInt64Value ∧ ¬ int1.isUInt64Value ∧
    int1.isIntegerValue
  )
  assertEq (-18446744073709551616) (← int1.getIntegerValue)
  assertEq (-1) (← int1.getRealOrIntegerValueSign)
  assertTrue (
    ¬ int2.isInt32Value ∧ ¬ int2.isUInt32Value ∧ ¬ int2.isInt64Value ∧ ¬ int2.isUInt64Value ∧
    int2.isIntegerValue
  )
  assertEq (-18446744073709551615) (← int2.getIntegerValue)
  assertTrue (
    ¬ int3.isInt32Value ∧ ¬ int3.isUInt32Value ∧ int3.isInt64Value ∧ ¬ int3.isUInt64Value ∧
    int3.isIntegerValue
  )
  assertEq (-4294967296) (← int3.getInt64Value)
  assertEq (-4294967296) (← int3.getIntegerValue)
  assertTrue (
    ¬ int4.isInt32Value ∧ ¬ int4.isUInt32Value ∧ int4.isInt64Value ∧ ¬ int4.isUInt64Value ∧
    int4.isIntegerValue
  )
  assertEq (-4294967295) (← int4.getInt64Value)
  assertEq (-4294967295) (← int4.getIntegerValue)
  assertTrue (
    int5.isInt32Value ∧ ¬ int5.isUInt32Value ∧ int5.isInt64Value ∧ ¬ int5.isUInt64Value ∧
    int5.isIntegerValue
  )
  assertEq (-10) (← int5.getInt32Value)
  assertEq (-10) (← int5.getInt64Value)
  assertEq (-10) (← int5.getIntegerValue)
  assertTrue (
    int6.isInt32Value ∧ int6.isUInt32Value ∧ int6.isInt64Value ∧ int6.isUInt64Value ∧
    int6.isIntegerValue
  )
  assertEq 0 (← int6.getUInt32Value)
  assertEq 0 (← int6.getUInt64Value)
  assertEq 0 (← int6.getInt32Value)
  assertEq 0 (← int6.getInt64Value)
  assertEq 0 (← int6.getIntegerValue)
  assertEq 0 (← int6.getRealOrIntegerValueSign)
  assertTrue (
    int7.isInt32Value ∧ int7.isUInt32Value ∧ int7.isInt64Value ∧ int7.isUInt64Value ∧
    int7.isIntegerValue
  )
  assertEq 10 (← int7.getUInt32Value)
  assertEq 10 (← int7.getUInt64Value)
  assertEq 10 (← int7.getInt32Value)
  assertEq 10 (← int7.getInt64Value)
  assertEq 10 (← int7.getIntegerValue)
  assertEq 1 (← int7.getRealOrIntegerValueSign)
  assertTrue (
    ¬ int8.isInt32Value ∧ int8.isUInt32Value ∧ int8.isInt64Value ∧ int8.isUInt64Value ∧
    int8.isIntegerValue
  )
  assertEq 4294967295 (← int8.getUInt32Value)
  assertEq 4294967295 (← int8.getUInt64Value)
  assertEq 4294967295 (← int8.getInt64Value)
  assertEq 4294967295 (← int8.getIntegerValue)
  assertTrue (
    ¬ int9.isInt32Value ∧ ¬ int9.isUInt32Value ∧ int9.isInt64Value ∧ int9.isUInt64Value ∧
    int9.isIntegerValue
  )
  assertEq 4294967296 (← int9.getUInt64Value)
  assertEq 4294967296 (← int9.getInt64Value)
  assertEq 4294967296 (← int9.getIntegerValue)
  assertTrue (
    ¬ int10.isInt32Value ∧ ¬ int10.isUInt32Value ∧ ¬ int10.isInt64Value ∧ int10.isUInt64Value ∧
    int10.isIntegerValue
  )
  assertEq 18446744073709551615 (← int10.getUInt64Value)
  assertEq 18446744073709551615 (← int10.getIntegerValue)
  assertTrue (
    ¬ int11.isInt32Value ∧ ¬ int11.isUInt32Value ∧ ¬ int11.isInt64Value ∧ ¬ int11.isUInt64Value ∧
    int11.isIntegerValue
  )
  assertEq 18446744073709551616 (← int11.getIntegerValue)

  -- `int12` not used in the original test
  let _ := int12

-- test![TestApiBlackTerm, getString] tm => do
--   let s1 ← tm.mkString "abcde"
--   assertTrue s1.isStringValue
--   assertEq "abcde" (← s1.getStringValue)

test![TestApiBlackTerm, getReal] tm => do
  let real1 ← tm.mkRealOfString "0"
  let real2 ← tm.mkRealOfString ".0"
  let real3 ← tm.mkRealOfString "-17"
  let real4 ← tm.mkRealOfString "-3/5"
  let real5 ← tm.mkRealOfString "12.7"
  let real6 ← tm.mkRealOfString "1/4294967297"
  let real7 ← tm.mkRealOfString "4294967297"
  let real8 ← tm.mkRealOfString "1/18446744073709551617"
  let real9 ← tm.mkRealOfString "18446744073709551617"
  let real10 ← tm.mkRealOfString "2343.2343"

  assertTrue (real1.isRealValue ∧ real1.isReal64Value ∧ real1.isReal32Value)
  assertTrue (real2.isRealValue ∧ real2.isReal64Value ∧ real2.isReal32Value)
  assertTrue (real3.isRealValue ∧ real3.isReal64Value ∧ real3.isReal32Value)
  assertTrue (real4.isRealValue ∧ real4.isReal64Value ∧ real4.isReal32Value)
  assertTrue (real5.isRealValue ∧ real5.isReal64Value ∧ real5.isReal32Value)
  assertTrue (real6.isRealValue ∧ real6.isReal64Value)
  assertTrue (real7.isRealValue ∧ real7.isReal64Value)
  assertTrue real8.isRealValue
  assertTrue real9.isRealValue
  assertTrue real10.isRealValue

  assertEq (0, 1) (← real1.getReal32Value)
  assertEq (0, 1) (← real1.getReal64Value)
  assertEq "0/1" (← real1.getRealValue)

  assertEq (0, 1) (← real2.getReal32Value)
  assertEq (0, 1) (← real2.getReal64Value)
  assertEq "0/1" (← real2.getRealValue)

  assertEq (-17, 1) (← real3.getReal32Value)
  assertEq (-17, 1) (← real3.getReal64Value)
  assertEq "-17/1" (← real3.getRealValue)

  assertEq (-3, 5) (← real4.getReal32Value)
  assertEq (-3, 5) (← real4.getReal64Value)
  assertEq "-3/5" (← real4.getRealValue)

  assertEq (127, 10) (← real5.getReal32Value)
  assertEq (127, 10) (← real5.getReal64Value)
  assertEq "127/10" (← real5.getRealValue)

  assertEq (1, 4294967297) (← real6.getReal64Value)
  assertEq "1/4294967297" (← real6.getRealValue)

  assertEq (4294967297, 1) (← real7.getReal64Value)
  assertEq "4294967297/1" (← real7.getRealValue)

  assertEq "1/18446744073709551617" (← real8.getRealValue)

  assertEq "18446744073709551617/1" (← real9.getRealValue)

  assertEq "23432343/10000" (← real10.getRealValue)

  tm.mkRealOfString "1/0" |> assertError
    "cannot construct Real or Int from string argument '1/0'"
  tm.mkRealOfString "2/0000" |> assertError
    "cannot construct Real or Int from string argument '2/0000'"

test![TestApiBlackTerm, getConstArrayBase] tm => do
  let int ← tm.getIntegerSort
  let arrSort ← tm.mkArraySort int int
  let one ← tm.mkInteger 1
  let constArr ← tm.mkConstArray arrSort one

  assertTrue constArr.isConstArray
  assertEq one (← constArr.getConstArrayBase)

  let a ← tm.mkConst arrSort "a"
  a.getConstArrayBase |> assertError
    "invalid argument 'a' for '*d_node', \
    expected Term to be a constant array when calling getConstArrayBase()"
  one.getConstArrayBase |> assertError
    "invalid argument '1' for '*d_node', \
    expected Term to be a constant array when calling getConstArrayBase()"

test![TestApiBlackTerm, getBoolean] tm => do
  let b1 ← tm.mkBoolean true
  let b2 ← tm.mkBoolean false

  assertTrue b1.isBooleanValue
  assertTrue b2.isBooleanValue
  assertTrue (← b1.getBooleanValue)
  assertFalse (← b2.getBooleanValue)

test![TestApiBlackTerm, getBitVector] tm => do
  let b1 ← tm.mkBitVector 8 15
  let b2 ← tm.mkBitVectorOfString 8 "00001111" 2
  let b3 ← tm.mkBitVectorOfString 8 "15" 10
  let b4 ← tm.mkBitVectorOfString 8 "0f" 16
  let b5 ← tm.mkBitVectorOfString 9 "00001111" 2
  let b6 ← tm.mkBitVectorOfString 9 "15" 10
  let b7 ← tm.mkBitVectorOfString 9 "0f" 16

  assertTrue b1.isBitVectorValue
  assertTrue b2.isBitVectorValue
  assertTrue b3.isBitVectorValue
  assertTrue b4.isBitVectorValue
  assertTrue b5.isBitVectorValue
  assertTrue b6.isBitVectorValue
  assertTrue b7.isBitVectorValue

  assertEq "00001111" (← b1.getBitVectorValue 2)
  assertEq "15" (← b1.getBitVectorValue 10)
  assertEq "f" (← b1.getBitVectorValue 16)
  assertEq "00001111" (← b2.getBitVectorValue 2)
  assertEq "15" (← b2.getBitVectorValue 10)
  assertEq "f" (← b2.getBitVectorValue 16)
  assertEq "00001111" (← b3.getBitVectorValue 2)
  assertEq "15" (← b3.getBitVectorValue 10)
  assertEq "f" (← b3.getBitVectorValue 16)
  assertEq "00001111" (← b4.getBitVectorValue 2)
  assertEq "15" (← b4.getBitVectorValue 10)
  assertEq "f" (← b4.getBitVectorValue 16)
  assertEq "000001111" (← b5.getBitVectorValue 2)
  assertEq "15" (← b5.getBitVectorValue 10)
  assertEq "f" (← b5.getBitVectorValue 16)
  assertEq "000001111" (← b6.getBitVectorValue 2)
  assertEq "15" (← b6.getBitVectorValue 10)
  assertEq "f" (← b6.getBitVectorValue 16)
  assertEq "000001111" (← b7.getBitVectorValue 2)
  assertEq "15" (← b7.getBitVectorValue 10)
  assertEq "f" (← b7.getBitVectorValue 16)

test![TestApiBlackTerm, isFiniteFieldValue] tm => do
  let fS ← tm.mkFiniteFieldSort 7
  let fV ← tm.mkFiniteFieldElem 1 fS
  assertTrue fV.isFiniteFieldValue
  let b1 ← tm.mkBitVector 8 15
  assertFalse b1.isFiniteFieldValue

test![TestApiBlackTerm, getFiniteFieldValue] tm => do
  let fS ← tm.mkFiniteFieldSort 7
  let fV ← tm.mkFiniteFieldElem 1 fS
  assertEq 1 (← fV.getFiniteFieldValue)
  Term.null () |>.getFiniteFieldValue |> assertError
    "invalid call to 'std::string cvc5::Term::getFiniteFieldValue() const', \
    expected non-null object"
  let b1 ← tm.mkBitVector 8 15
  b1.getFiniteFieldValue |> assertError
    "invalid argument '#b00001111' for '*d_node', \
    expected Term to be a finite field value when calling getFiniteFieldValue()"

test![TestApiBlackTerm, getUninterpretedSortValue] tm solver => do
  solver.setOption "produce-models" "true"
  let x ← tm.mkConst uninterpreted "x"
  let y ← tm.mkConst uninterpreted "y"
  tm.mkTerm Kind.EQUAL #[x, y] >>= solver.assertFormula
  assertTrue (← solver.checkSat).isSat
  let vx ← solver.getValue x
  let vy ← solver.getValue y
  assertTrue vx.isUninterpretedSortValue
  assertTrue vy.isUninterpretedSortValue
  assertEq (← vx.getUninterpretedSortValue) (← vy.getUninterpretedSortValue)

test![TestApiBlackTerm, getRoundingModeValue] tm => do
  assertFalse (← tm.mkInteger 15).isRoundingModeValue
  assertTrue (← tm.mkRoundingMode RoundingMode.ROUND_NEAREST_TIES_TO_EVEN).isRoundingModeValue
  assertFalse (← tm.mkConst (← tm.getRoundingModeSort)).isRoundingModeValue

test![TestApiBlackTerm, getRoundingModeValue] tm => do
  (← tm.mkInteger 15).getRoundingModeValue |> assertError
    "invalid argument '15' for '*d_node', \
    expected Term to be a floating-point rounding mode value when calling getRoundingModeValue()"
  assertEq RoundingMode.ROUND_NEAREST_TIES_TO_EVEN
    (← (← tm.mkRoundingMode RoundingMode.ROUND_NEAREST_TIES_TO_EVEN).getRoundingModeValue)
  assertEq RoundingMode.ROUND_TOWARD_POSITIVE
    (← (← tm.mkRoundingMode RoundingMode.ROUND_TOWARD_POSITIVE).getRoundingModeValue)
  assertEq RoundingMode.ROUND_TOWARD_NEGATIVE
    (← (← tm.mkRoundingMode RoundingMode.ROUND_TOWARD_NEGATIVE).getRoundingModeValue)
  assertEq RoundingMode.ROUND_TOWARD_ZERO
    (← (← tm.mkRoundingMode RoundingMode.ROUND_TOWARD_ZERO).getRoundingModeValue)
  assertEq RoundingMode.ROUND_NEAREST_TIES_TO_AWAY
    (← (← tm.mkRoundingMode RoundingMode.ROUND_NEAREST_TIES_TO_AWAY).getRoundingModeValue)

test![TestApiBlackTerm, getTuple] tm => do
  let t1 ← tm.mkInteger 15
  let t2 ← tm.mkReal 17 25
  let t3 ← tm.mkString "abc"

  let tup ← tm.mkTuple #[t1, t2, t3]

  assertTrue tup.isTupleValue
  assertEq #[t1, t2, t3] (← tup.getTupleValue)

test![TestApiBlackTerm, getFloatingPoint] tm => do
  let bvVal ← tm.mkBitVectorOfString 16 "0000110000000011" 2
  let fp ← tm.mkFloatingPoint 5 11 bvVal

  assertTrue fp.isFloatingPointValue
  assertFalse fp.isFloatingPointPosZero
  assertFalse fp.isFloatingPointNegZero
  assertFalse fp.isFloatingPointPosInf
  assertFalse fp.isFloatingPointNegInf
  assertFalse fp.isFloatingPointNaN
  assertEq (5, 11, bvVal) (← fp.getFloatingPointValue)

  assertTrue (← tm.mkFloatingPointPosZero 5 11).isFloatingPointPosZero
  assertTrue (← tm.mkFloatingPointNegZero 5 11).isFloatingPointNegZero
  assertTrue (← tm.mkFloatingPointPosInf 5 11).isFloatingPointPosInf
  assertTrue (← tm.mkFloatingPointNegInf 5 11).isFloatingPointNegInf
  assertTrue (← tm.mkFloatingPointNaN 5 11).isFloatingPointNaN

test![TestApiBlackTerm, getSet] tm solver => do
  let s ← tm.mkSetSort int

  let i1 ← tm.mkInteger 5
  let i2 ← tm.mkInteger 7

  let s1 ← tm.mkEmptySet s
  let s2 ← tm.mkTerm Kind.SET_SINGLETON #[i1]
  let s3 ← tm.mkTerm Kind.SET_SINGLETON #[i1]
  let s4 ← tm.mkTerm Kind.SET_SINGLETON #[i2]
  let mut s5 ← tm.mkTerm Kind.SET_UNION #[s2, ← tm.mkTerm Kind.SET_UNION #[s3, s4]]

  assertTrue s1.isSetValue
  assertTrue s2.isSetValue
  assertTrue s3.isSetValue
  assertTrue s4.isSetValue
  assertFalse s5.isSetValue
  s5 ← solver.simplify s5
  assertTrue s5.isSetValue

  assertEq #[] (← s1.getSetValue)
  assertEq #[i1] (← s2.getSetValue)
  assertEq #[i1] (← s3.getSetValue)
  assertEq #[i2] (← s4.getSetValue)
  assertEq #[i1, i2] (← s5.getSetValue)

test![TestApiBlackTerm, getSequence] tm solver => do
  let s ← tm.mkSequenceSort int

  let i1 ← tm.mkInteger 5
  let i2 ← tm.mkInteger 7

  let s1 ← tm.mkEmptySequence s
  let mut s2 ← tm.mkTerm Kind.SEQ_UNIT #[i1]
  let mut s3 ← tm.mkTerm Kind.SEQ_UNIT #[i1]
  let mut s4 ← tm.mkTerm Kind.SEQ_UNIT #[i2]
  let mut s5 ← tm.mkTerm Kind.SEQ_CONCAT #[s2, ← tm.mkTerm Kind.SEQ_CONCAT #[s3, s4]]

  assertTrue s1.isSequenceValue
  assertFalse s2.isSequenceValue
  assertFalse s3.isSequenceValue
  assertFalse s4.isSequenceValue
  assertFalse s5.isSequenceValue

  s2 ← solver.simplify s2
  s3 ← solver.simplify s3
  s4 ← solver.simplify s4
  s5 ← solver.simplify s5

  assertEq #[] (← s1.getSequenceValue)
  assertEq #[i1] (← s2.getSequenceValue)
  assertEq #[i1] (← s3.getSequenceValue)
  assertEq #[i2] (← s4.getSequenceValue)
  assertEq #[i1, i1, i2] (← s5.getSequenceValue)

test![TestApiBlackTerm, substitute] tm => do
  let int ← tm.getIntegerSort
  let x ← tm.mkConst int "x"
  let one ← tm.mkInteger 1
  let tru ← tm.mkTrue
  let xPx ← tm.mkTerm Kind.ADD #[x, x]
  let onePone ← tm.mkTerm Kind.ADD #[one, one]

  assertEq onePone (← xPx.substitute #[x] #[one])
  assertEq xPx (← onePone.substitute #[one] #[x])
  -- incorrect due to type
  xPx.substitute #[one] #[tru] |> assertError "expecting terms of the same sort at index 0"

  -- simultaneous substitution
  let y ← tm.mkConst int "y"
  let xPy ← tm.mkTerm Kind.ADD #[x, y]
  let yPone ← tm.mkTerm Kind.ADD #[y, one]
  let es := #[x, y]
  let rs := #[y, one]
  assertEq yPone (← xPy.substitute es rs)

  -- incorrect substitution due to arity
  let rs := rs.pop
  xPy.substitute es rs |> assertError "expected vectors of the same arity in substitute"

  -- incorrect substitution due to types
  let rs := rs.push tru
  xPy.substitute es rs |> assertError "expecting terms of the same sort at index 1"

  -- null cannot substitute
  let n := Term.null ()
  n.substitute #[one] #[x] |> assertError
    "invalid call to 'Term cvc5::Term::substitute(const std::vector<Term> &, \
    const std::vector<Term> &) const', expected non-null object"
  xPx.substitute #[n] #[x] |> assertError "invalid null term in 'terms' at index 0"
  xPx.substitute #[x] #[n] |> assertError "invalid null term in 'replacements' at index 0"
  let rs := rs.pop.push n
  xPy.substitute es rs |> assertError "invalid null term in 'replacements' at index 1"
  let es := #[x]
  let rs := #[y]
  n.substitute es rs |> assertError
    "invalid call to 'Term cvc5::Term::substitute(const std::vector<Term> &, \
    const std::vector<Term> &) const', expected non-null object"
  let es := es.push n
  let rs := rs.push one
  xPx.substitute es rs |> assertError "invalid null term in 'terms' at index 1"

test![TestApiBlackTerm, constArray] tm => do
  let int ← tm.getIntegerSort
  let arrSort ← tm.mkArraySort int int
  let a ← tm.mkConst arrSort "a"
  let one ← tm.mkInteger 1
  let two ← tm.mkBitVector 2 2
  let iConst ← tm.mkConst int
  let constArr ← tm.mkConstArray arrSort one

  tm.mkConstArray arrSort two |> assertError "value does not match element sort"
  tm.mkConstArray arrSort iConst |> assertError "invalid argument '||' for 'val', expected a value"

  assertEq Kind.CONST_ARRAY (← constArr.getKind)
  assertEq one (← constArr.getConstArrayBase)
  a.getConstArrayBase |> assertError
    "invalid argument 'a' for '*d_node', \
    expected Term to be a constant array when calling getConstArrayBase()"

  let real ← tm.getRealSort
  let arrSort ← tm.mkArraySort real real
  let zeroArray ← tm.mkReal 0 >>= tm.mkConstArray arrSort
  let stores ← tm.mkTerm Kind.STORE #[zeroArray, ← tm.mkReal 1, ← tm.mkReal 2]
  let stores ← tm.mkTerm Kind.STORE #[stores, ← tm.mkReal 2, ← tm.mkReal 3]
  let _ ← tm.mkTerm Kind.STORE #[stores, ← tm.mkReal 4, ← tm.mkReal 5]

test![TestApiBlackTerm, getSequenceValue] tm => do
  let real ← tm.getRealSort
  let seq ← tm.mkSequenceSort real
  let s ← tm.mkEmptySequence seq

  assertEq Kind.CONST_SEQUENCE (← s.getKind)
  -- empty sequence has zero elements
  let cs ← s.getSequenceValue
  assertTrue cs.isEmpty

  -- a seq.unit app is not a constant sequence (regardless of whether it is applied to constant)
  let su ← tm.mkTerm Kind.SEQ_UNIT #[← tm.mkReal 1]
  su.getSequenceValue |> assertError
    "invalid argument '(seq.unit 1.0)' for '*d_node', \
    expected Term to be a sequence value when calling getSequenceValue()"

test![TestApiBlackTerm, getCardinalityConstraint] tm => do
  let su ← tm.mkUninterpretedSort "u"
  let t ← tm.mkCardinalityConstraint su 3
  assertTrue t.isCardinalityConstraint
  let cc ← t.getCardinalityConstraint
  assertEq su cc.fst
  assertEq 3 cc.snd
  let x ← tm.mkConst (← tm.getIntegerSort) "x"
  assertFalse x.isCardinalityConstraint
  x.getCardinalityConstraint |> assertError
    "invalid argument 'x' for '*d_node', \
    expected Term to be a cardinality constraint when calling getCardinalityConstraint()"
  -- original test checks that the following produces an error, but the lean version does not
  Term.null () |>.isCardinalityConstraint |> assertFalse

test![TestApiBlackTerm, getRealAlgebraicNumber] tm solver => do
  solver.setOption "produce-models" "true"
  solver.setLogic "QF_NRA"
  let realSort ← tm.getRealSort
  let x ← tm.mkConst realSort "x"
  let x2 ← tm.mkTerm Kind.MULT #[x, x]
  let two ← tm.mkReal 2 1
  let eq ← tm.mkTerm Kind.EQUAL #[x2, two]
  solver.assertFormula eq
  -- note that check-sat should only return *sat* if libpoly is enabled.
  -- otherwise, we do not test the following functionality
  if (← solver.checkSat).isSat then
    -- we find a model for `(x*x = 2)`, where x should be a real algebraic number
    -- we assert that its defining polynomial is non-null and its lower and upper bounds are reals
    let vx ← solver.getValue x
    assertTrue vx.isRealAlgebraicNumber
    let y ← tm.mkVar realSort "y"
    let poly ← vx.getRealAlgebraicNumberDefiningPolynomial y
    assertFalse poly.isNull
    let lb ← vx.getRealAlgebraicNumberLowerBound
    assertTrue lb.isRealValue
    let ub ← vx.getRealAlgebraicNumberUpperBound
    assertTrue ub.isRealValue
    -- cannot call with non-variable
    let yc ← tm.mkConst realSort "y"
    vx.getRealAlgebraicNumberDefiningPolynomial yc |> assertError
      "invalid argument 'y' for 'v', expected expected a variable as argument \
      when calling getRealAlgebraicNumberDefiningPolynomial()"

test![TestApiBlackTerm, getSkolem] tm => do
  -- ordinary variables are not skolems
  let x ← tm.mkConst (← tm.getIntegerSort) "x"
  assertFalse x.isSkolem
  x.getSkolemId |> assertError
    "invalid argument 'x' for '*d_node', expected Term to be a skolem when calling getSkolemId"
  x.getSkolemIndices |> assertError
    "invalid argument 'x' for '*d_node', expected Term to be a skolem when calling getSkolemIndices"

test![TestApiBlackTerm, toString] tm => do
  assertEq "null" (Term.null () |>.toString)

  let int ← tm.getIntegerSort
  let x ← tm.mkConst int "x"

  let _ := s!"{#[x, x]}"
