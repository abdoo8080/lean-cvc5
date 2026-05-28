/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Adrien Champion
-/

import cvc5Test.Init

/-! # Black box testing of the `Solver` type

- <https://github.com/cvc5/cvc5/blob/main/test/unit/api/cpp/api_solver_black.cpp>
-/

namespace cvc5.Test

test![TestApiBlackSolver, pow2Large1] tm solver => do
  -- Based on https://github.com/cvc5/cvc5-projects/issues/371
  let string ← tm.getStringSort
  let s4 ← tm.mkArraySort string int
  let s7 ← tm.mkArraySort int string
  let t10 ← tm.mkIntegerOfString "68038927088685865242724985643"
  let t74 ← tm.mkIntegerOfString "8416288636405"
  let mut ctors := #[]
  let mut dtConsDecl ← tm.mkDatatypeConstructorDecl "_x109"
  dtConsDecl ← dtConsDecl.addSelector "_x108" s7
  ctors := ctors.push dtConsDecl
  dtConsDecl ← tm.mkDatatypeConstructorDecl "_x113"
  dtConsDecl ← dtConsDecl.addSelector "_x110" s4
  dtConsDecl ← dtConsDecl.addSelector "_x111" int
  dtConsDecl ← dtConsDecl.addSelector "_x112" s7
  ctors := ctors.push dtConsDecl
  let s11 ← solver.declareDatatype "_x107" ctors
  let t82 ← tm.mkConst s11 "_x114"
  let t180 ← tm.mkTerm Kind.POW2 #[t10]
  let t258 ← tm.mkTerm Kind.GEQ #[t74, t180]
  solver.assertFormula t258
  solver.simplify t82 true |> assertError
    "The exponent of the POW(^) operator can only be a positive integral constant below 67108864. \
    Exception occurred in:\n  \
    (int.pow2 68038927088685865242724985643)"

test![TestApiBlackSolver, pow2Large2] tm solver => do
  -- Based on https://github.com/cvc5/cvc5-projects/issues/333
  let t1 ← tm.mkBitVector 63 <| (1 : UInt64) <<< 62
  let t2 ← tm.mkTerm Kind.BITVECTOR_UBV_TO_INT #[t1]
  let t3 ← tm.mkTerm Kind.POW2 #[t2]
  let t4 ← tm.mkTerm Kind.DISTINCT #[t3, t2]
  solver.checkSatAssuming #[t4] |> assertError
    "The exponent of the POW(^) operator can only be a positive integral constant below 67108864. \
    Exception occurred in:\n  \
    (int.pow2 4611686018427387904)"

test![TestApiBlackSolver, pow2Large3] tm solver => do
  -- Based on https://github.com/cvc5/cvc5-projects/issues/339
  let t203 ← tm.mkIntegerOfString "6135470354240554220207"
  let t262 ← tm.mkTerm Kind.POW2 #[t203]
  let t536 ← tm.mkTermOfOp (← tm.mkOp Kind.INT_TO_BITVECTOR #[49]) #[t262]
  -- should not throw an exception, will not simplify
  solver.simplify t536 |> assertOkDiscard

test![TestApiBlackSolver, recoverableException] tm solver => do
  solver.setOption "produce-models" "true"
  let x ← tm.mkConst (← tm.getBooleanSort) "x"
  solver.assertFormula (← (← x.eqTerm x).notTerm)
  solver.getValue x |> assertError
    "cannot get value unless after a SAT or UNKNOWN response."

test![TestApiBlackSolver, simplify] tm solver => do
  let bvSort ← tm.mkBitVectorSort 32
  let funSort1 ← tm.mkFunctionSort #[bvSort, bvSort] bvSort
  let funSort2 ← tm.mkFunctionSort #[uninterpreted] int
  let consListSort ← do
    let mut consListSpec ← tm.mkDatatypeDecl "list"
    let mut cons ← tm.mkDatatypeConstructorDecl "cons"
    cons ← cons.addSelector "head" int
    cons ← cons.addSelectorSelf "tail"
    consListSpec ← consListSpec.addConstructor cons
    let nil ← tm.mkDatatypeConstructorDecl "nil"
    consListSpec ← consListSpec.addConstructor nil
    tm.mkDatatypeSort consListSpec

  let x ← tm.mkConst bvSort "x"
  solver.simplify x |> assertOkDiscard
  let a ← tm.mkConst bvSort "a"
  solver.simplify a |> assertOkDiscard
  let b ← tm.mkConst bvSort "b"
  solver.simplify b |> assertOkDiscard
  let tru ← tm.mkTrue
  let x_eq_x ← tm.mkTerm Kind.EQUAL #[x, x]
  assertNe tru x_eq_x
  assertEq tru (← solver.simplify x_eq_x)
  let x_eq_b ← tm.mkTerm Kind.EQUAL #[x, b]
  assertNe tru x_eq_b
  assertNe tru (← solver.simplify x_eq_b)

  let i1 ← tm.mkConst int "i1"
  solver.simplify i1 |> assertOkDiscard
  let i2 ← tm.mkTerm Kind.MULT #[i1, ← tm.mkInteger 23]
  solver.simplify i2 |> assertOkDiscard
  assertNe i1 i2
  assertNe i1 (← solver.simplify i2)
  let i3 ← tm.mkTerm Kind.ADD #[i1, ← tm.mkInteger 0]
  solver.simplify i3 |> assertOkDiscard
  assertNe i1 i3
  assertEq i1 (← solver.simplify i3)

  let consList ← consListSort.getDatatype
  let cons ← consList.getConstructor "cons"
  let nil ← consList.getConstructor "nil"
  let dt1 ← tm.mkTerm Kind.APPLY_CONSTRUCTOR #[
    ← cons.getTerm,
    ← tm.mkInteger 0,
    ← tm.mkTerm Kind.APPLY_CONSTRUCTOR #[← nil.getTerm],
  ]
  solver.simplify dt1 |> assertOkDiscard
  let dt2 ← tm.mkTerm Kind.APPLY_SELECTOR #[
    ← cons.getSelector "head" >>= DatatypeSelector.getTerm,
    dt1
  ]
  solver.simplify dt2 |> assertOkDiscard

  let b1 ← tm.mkVar bvSort "b1"
  solver.simplify b1 |> assertOkDiscard
  let b2 ← tm.mkVar bvSort "b1"
  solver.simplify b2 |> assertOkDiscard
  let b3 ← tm.mkVar uninterpreted "b3"
  solver.simplify b3 |> assertOkDiscard
  let v1 ← tm.mkVar bvSort "v1"
  solver.simplify v1 |> assertOkDiscard
  let v2 ← tm.mkVar int "v2"
  solver.simplify v2 |> assertOkDiscard
  let f1 ← tm.mkVar funSort1 "f1"
  solver.simplify f1 |> assertOkDiscard
  let f2 ← tm.mkVar funSort2 "f2"
  solver.simplify f2 |> assertOkDiscard
  solver.defineFunsRec #[f1, f2] #[#[b1, b2], #[b3]] #[v1, v2]
  solver.simplify f1 |> assertOkDiscard
  solver.simplify f2 |> assertOkDiscard

  let tm' ← TermManager.new
  let solver' ← Solver.new tm'
  solver'.simplify x |> assertError
    "Given term is not associated with the term manager of this solver"

test![TestApiBlackSolver, simplifyApplySubs] tm solver => do
  solver.setOption "incremental" "true"
  let x ← tm.mkConst int "x"
  let zero ← tm.mkInteger 0
  let eq ← tm.mkTerm Kind.EQUAL #[x, zero]
  solver.assertFormula eq
  solver.checkSat |> assertOkDiscard

  assertEq x (← solver.simplify x false)
  assertEq zero (← solver.simplify x true)

test![TestApiBlackSolver, assertFormula] tm solver => do
  solver.assertFormula (← tm.mkTrue) |> assertOkDiscard
  solver.assertFormula (Term.null ()) |> assertError
    "invalid null argument for 'term'"
  let tm' ← TermManager.new
  let solver' ← Solver.new tm'
  solver'.assertFormula (← tm.mkTrue) |> assertError
    "Given term is not associated with the term manager of this solver"

test![TestApiBlackSolver, checkSatAssuming] tm solver => do
  solver.setOption "incremental" "false"
  solver.checkSatAssuming #[← tm.mkTrue] |> assertOkDiscard
  solver.checkSatAssuming #[← tm.mkTrue] |> assertError
    "cannot make multiple queries unless incremental solving is enabled (try --incremental)"
  let tm' ← TermManager.new
  let solver' ← Solver.new tm'
  solver'.checkSatAssuming #[← tm.mkTrue] |> assertError
    "invalid term in 'assumptions' at index 0, \
    expected a term associated with the term manager of this solver"

test![TestApiBlackSolver, checkSatAssuming1] tm solver => do
  let x ← tm.mkConst bool "x"
  let y ← tm.mkConst bool "y"
  let z ← tm.mkTerm Kind.AND #[x, y]
  solver.setOption "incremental" "true"
  solver.checkSatAssuming #[← tm.mkTrue] |> assertOkDiscard
  solver.checkSatAssuming #[Term.null ()] |> assertError
    "invalid null term in 'assumptions' at index 0"
  solver.checkSatAssuming #[← tm.mkTrue] |> assertOkDiscard
  solver.checkSatAssuming #[z] |> assertOkDiscard

test![TestApiBlackSolver, checkSatAssuming2] tm solver => do
  solver.setOption "incremental" "true"

  let uToIntSort ← tm.mkFunctionSort #[uninterpreted] int
  let intPredSort ← tm.mkFunctionSort #[int] bool

  let n := Term.null ()
  -- constants
  let x ← tm.mkConst uninterpreted "x"
  let y ← tm.mkConst uninterpreted "y"
  -- functions
  let f ← tm.mkConst uToIntSort "f"
  let p ← tm.mkConst intPredSort "p"
  -- values
  let zero ← tm.mkInteger 0
  let one ← tm.mkInteger 1
  -- terms
  let f_x ← tm.mkTerm Kind.APPLY_UF #[f, x]
  let f_y ← tm.mkTerm Kind.APPLY_UF #[f, y]
  let sum ← tm.mkTerm Kind.ADD #[f_x, f_y]
  let p_0 ← tm.mkTerm Kind.APPLY_UF #[p, zero]
  let p_f_y ← tm.mkTerm Kind.APPLY_UF #[p, f_y]
  -- assertions
  let assertions ← tm.mkTerm Kind.AND #[
    ← tm.mkTerm Kind.LEQ #[zero, f_x], -- `0 ≤ f(x)`
    ← tm.mkTerm Kind.LEQ #[zero, f_y], -- `0 ≤ f(y)`
    ← tm.mkTerm Kind.LEQ #[sum, one], -- `f(x) + f(y) ≤ 1`
    ← p_0.notTerm, -- `¬ p(0)`
    p_f_y, -- `p(f(y))`
  ]

  solver.checkSatAssuming #[← tm.mkTrue] |> assertOkDiscard
  solver.assertFormula assertions
  solver.checkSatAssuming #[← tm.mkTerm Kind.DISTINCT #[x, y]] |> assertOkDiscard
  solver.checkSatAssuming #[← tm.mkFalse, ← tm.mkTerm Kind.DISTINCT #[x, y]] |> assertOkDiscard
  solver.checkSatAssuming #[n] |> assertError
    "invalid null term in 'assumptions' at index 0"
  solver.checkSatAssuming #[n, ← tm.mkTerm Kind.DISTINCT #[x, y]] |> assertError
    "invalid null term in 'assumptions' at index 0"

test![TestApiBlackSolver, declareFunFresh] tm solver => do
  let t1 ← solver.declareFun "b" #[] bool true
  let t2 ← solver.declareFun "b" #[] bool false
  let t3 ← solver.declareFun "b" #[] bool false
  assertNe t1 t2
  assertNe t1 t3
  assertEq t2 t3
  let t4 ← solver.declareFun "c" #[] bool false
  assertNe t2 t4
  let t5 ← solver.declareFun "b" #[] int false
  assertNe t2 t5

  let tm' ← TermManager.new
  let solver' ← Solver.new tm'
  solver'.declareFun "b" #[] int false |> assertError
    "Given sort is not associated with the term manager of this solver"

test![TestApiBlackSolver, declareDatatype] tm solver => do
  let lin ← tm.mkDatatypeConstructorDecl "lin"
  let ctors0 := #[lin]
  solver.declareDatatype "" ctors0 |> assertOkDiscard

  let nil ← tm.mkDatatypeConstructorDecl "nil"
  let ctors1 := #[nil]
  solver.declareDatatype "a" ctors1 |> assertOkDiscard

  let cons ← tm.mkDatatypeConstructorDecl "cons"
  let nil2 ← tm.mkDatatypeConstructorDecl "nil"
  let ctors2 := #[cons, nil2]
  solver.declareDatatype "b" ctors2 |> assertOkDiscard

  let cons2 ← tm.mkDatatypeConstructorDecl "cons"
  let nil3 ← tm.mkDatatypeConstructorDecl "nil"
  let ctors3 := #[cons2, nil3]
  solver.declareDatatype "" ctors3 |> assertOkDiscard

  -- must have at least one constructor
  let mut ctors4 := #[]
  solver.declareDatatype "c" ctors4 |> assertError
    "invalid argument '[]' for 'ctors', \
    expected a datatype declaration with at least one constructor"
  -- constructor may not be reused
  let ctor1 ← tm.mkDatatypeConstructorDecl "_x21"
  let ctor2 ← tm.mkDatatypeConstructorDecl "_x31"
  solver.declareDatatype "_x17" #[ctor1, ctor2] |> assertOkDiscard
  solver.declareDatatype "_x86" #[ctor1, ctor2] |> assertError
    "cannot use a constructor for multiple datatypes"

  let tm' ← TermManager.new
  let solver' ← Solver.new tm'
  let nnil ← tm.mkDatatypeConstructorDecl "nil"
  solver'.declareDatatype "a" #[nnil] |> assertError
    "invalid datatype constructor declaration in 'ctorsr' at index 0, \
    expected a datatype constructor declaration associated with \
    the term manager of this solver object"

test![TestApiBlackSolver, declareFun] tm solver => do
  let bvSort ← tm.mkBitVectorSort 32
  let funSort ← tm.mkFunctionSort #[uninterpreted] int
  solver.declareFun "f1" #[] bvSort |> assertOkDiscard
  solver.declareFun "f3" #[bvSort, int] bvSort |> assertOkDiscard
  solver.declareFun "f2" #[] funSort |> assertError
    "invalid argument '(-> u Int)' for 'sort', expected non-function sort as codomain sort"
  -- functions as arguments is allowed
  solver.declareFun "f4" #[bvSort, funSort] bvSort |> assertOkDiscard
  solver.declareFun "f5" #[bvSort, bvSort] funSort |> assertError
    "invalid argument '(-> u Int)' for 'sort', expected non-function sort as codomain sort"

test![TestApiBlackSolver, declareSort] tm solver => do
  solver.declareSort "s" 0 |> assertOkDiscard
  solver.declareSort "s" 2 |> assertOkDiscard
  solver.declareSort "" 2 |> assertOkDiscard

test![TestApiBlackSolver, declareSortFresh] tm solver => do
  let t1 ← solver.declareSort "b" 0 true
  let t2 ← solver.declareSort "b" 0 false
  let t3 ← solver.declareSort "b" 0 false
  assertNe t1 t2
  assertNe t1 t3
  assertEq t2 t3
  let t4 ← solver.declareSort "c" 0 false
  assertNe t2 t4
  let t5 ← solver.declareSort "b" 1 false
  assertNe t2 t5

test![TestApiBlackSolver, defineFun] tm solver => do
  let bvSort ← tm.mkBitVectorSort 32
  let funSort ← tm.mkFunctionSort #[uninterpreted] int
  let b1 ← tm.mkVar bvSort "b1"
  let b2 ← tm.mkVar int "b2"
  let b3 ← tm.mkVar funSort "b3"
  let v1 ← tm.mkConst bvSort "v1"
  let v2 ← tm.mkConst funSort "v2"
  solver.defineFun "f" #[] bvSort v1 |> assertOkDiscard
  solver.defineFun "ff" #[b1, b2] bvSort v1 |> assertOkDiscard
  solver.defineFun "ff" #[v1, b2] bvSort v1 |> assertError
    "invalid bound variable in 'bound_vars' at index 0, expected a bound variable"
  solver.defineFun "fff" #[b1] bvSort v2 |> assertError
    "invalid sort of function body 'v2', expected '(_ BitVec 32)', found '(-> u Int)'"
  solver.defineFun "ffff" #[b1] funSort v2 |> assertError
    "invalid argument '(-> u Int)' for 'sort', expected non-function sort as codomain sort"
  -- b3 has function sort, which is allowed as an argument
  solver.defineFun "fffff" #[b1, b3] bvSort v1 |> assertOkDiscard

  let tm' ← TermManager.new
  let solver' ← Solver.new tm'
  let bvSort' ← tm'.mkBitVectorSort 32
  let v1' ← tm'.mkConst bvSort' "v1"
  let b1' ← tm'.mkVar bvSort' "b1"
  let b2' ← tm'.mkVar (← tm'.getIntegerSort) "b2"
  solver'.defineFun "f" #[] bvSort v1' |> assertError
    "Given sort is not associated with the term manager of this solver"
  solver'.defineFun "f" #[] bvSort' v1 |> assertError
    "Given term is not associated with the term manager of this solver"
  solver'.defineFun "ff" #[b1, b2'] bvSort' v1' |> assertError
    "invalid term in 'bound_vars' at index 0, \
    expected a term associated with the term manager of this solver"
  solver'.defineFun "ff" #[b1', b2] bvSort' v1' |> assertError
    "invalid term in 'bound_vars' at index 1, \
    expected a term associated with the term manager of this solver"
  solver'.defineFun "ff" #[b1', b2'] bvSort v1' |> assertError
    "Given sort is not associated with the term manager of this solver"
  solver'.defineFun "ff" #[b1', b2'] bvSort' v1 |> assertError
    "Given term is not associated with the term manager of this solver"

test![TestApiBlackSolver, defineFunGlobal] tm solver => do
  let bTrue ← tm.mkBoolean true
  -- `(define-fun f () Bool true)`
  let f ← solver.defineFun "f" #[] bool bTrue true
  let b ← tm.mkVar bool "b"
  -- `(define-fun g (b Bool) Bool b)`
  let g ← solver.defineFun "g" #[b] bool b true

  -- `(assert (or (not f) (not (g true))))`
  tm.mkTerm Kind.OR #[
    ← f.notTerm, ← (← tm.mkTerm Kind.APPLY_UF #[g, bTrue]).notTerm
  ] >>= solver.assertFormula
  assertTrue (← solver.checkSat).isUnsat
  solver.resetAssertions
  -- `(assert (or (not f) (not (g true))))`
  tm.mkTerm Kind.OR #[
    ← f.notTerm, ← (← tm.mkTerm Kind.APPLY_UF #[g, bTrue]).notTerm
  ] >>= solver.assertFormula
  assertTrue (← solver.checkSat).isUnsat

  let tm' ← TermManager.new
  let solver' ← Solver.new tm'
  solver'.defineFun "f" #[] bool bTrue true |> assertError
    "Given sort is not associated with the term manager of this solver"

test![TestApiBlackSolver, defineFunRec] tm solver => do
  let bvSort ← tm.mkBitVectorSort 32
  let funSort1 ← tm.mkFunctionSort #[bvSort, bvSort] bvSort
  let funSort2 ← tm.mkFunctionSort #[uninterpreted] int
  let b1 ← tm.mkVar bvSort "b1"
  let b11 ← tm.mkVar bvSort "b1"
  let b2 ← tm.mkVar int "b2"
  let b3 ← tm.mkVar funSort2 "b3"
  let v1 ← tm.mkConst bvSort "v1"
  let v2 ← tm.mkConst int "v2"
  let v3 ← tm.mkConst funSort2 "v3"
  let f1 ← tm.mkConst funSort1 "f1"
  let f2 ← tm.mkConst funSort2 "f2"
  let f3 ← tm.mkConst bvSort "f3"
  solver.defineFunRec "f" #[] bvSort v1 |> assertOkDiscard
  solver.defineFunRec "ff" #[b1, b2] bvSort v1 |> assertOkDiscard
  solver.defineFunRecTerm f1 #[b1, b11] v1 |> assertOkDiscard
  solver.defineFunRec "fff" #[b1] bvSort v3 |> assertError
    "invalid sort of function body 'v3', expected '(_ BitVec 32)'"
  solver.defineFunRec "ff" #[b1, v2] bvSort v1 |> assertError
    "invalid bound variable in 'bound_vars' at index 1, expected a bound variable"
  solver.defineFunRec "ffff" #[b1] funSort2 v3 |> assertError
    "invalid argument '(-> u Int)' for 'sort', expected non-function sort as codomain sort"
  -- b3 has function sort, which is allowed as an argument
  solver.defineFunRec "fffff" #[b1, b3] bvSort v1 |> assertOkDiscard
  solver.defineFunRecTerm f1 #[b1] v1 |> assertError
    "invalid size of argument 'bound_vars', expected '2'"
  solver.defineFunRecTerm f1 #[b1, b11] v2 |> assertError
    "invalid sort of function body 'v2', expected '(_ BitVec 32)'"
  solver.defineFunRecTerm f1 #[b1, b11] v3 |> assertError
    "invalid sort of function body 'v3', expected '(_ BitVec 32)'"
  solver.defineFunRecTerm f2 #[b1] v2 |> assertError
    "invalid sort of parameter in 'bound_vars' at index 0, expected sort 'u'"
  solver.defineFunRecTerm f3 #[b1] v1 |> assertError
    "invalid argument 'f3' for 'fun', expected function or nullary symbol"

  let tm' ← TermManager.new
  let solver' ← Solver.new tm'
  let bvSort2 ← tm'.mkBitVectorSort 32
  let v12 ← tm'.mkConst bvSort2 "v1"
  let b12 ← tm'.mkVar bvSort2 "b1"
  let b22 ← tm'.mkVar (← tm'.getIntegerSort) "b2"
  solver'.defineFunRec "f" #[] bvSort2 v12 |> assertOkDiscard
  solver'.defineFunRec "ff" #[b12, b22] bvSort2 v12 |> assertOkDiscard
  solver'.defineFunRec "f" #[] bvSort v12 |> assertError
    "Given sort is not associated with the term manager of this solver"
  solver'.defineFunRec "f" #[] bvSort2 v1 |> assertError
    "Given term is not associated with the term manager of this solver"
  solver'.defineFunRec "ff" #[b1, b22] bvSort2 v12 |> assertError
    "invalid term in 'bound_vars' at index 0, \
    expected a term associated with the term manager of this solver"
  solver'.defineFunRec "ff" #[b12, b2] bvSort2 v12 |> assertError
    "invalid term in 'bound_vars' at index 1, \
    expected a term associated with the term manager of this solver"
  solver'.defineFunRec "ff" #[b12, b22] bvSort v12 |> assertError
    "Given sort is not associated with the term manager of this solver"
  solver'.defineFunRec "ff" #[b12, b22] bvSort2 v1 |> assertError
    "Given term is not associated with the term manager of this solver"

test![TestApiBlackSolver, defineFunRecWrongLogic] tm solver => do
  solver.setLogic "QF_BV"
  let bvSort ← tm.mkBitVectorSort 32
  let funSort ← tm.mkFunctionSort #[bvSort, bvSort] bvSort
  let b ← tm.mkVar bvSort "b"
  let v ← tm.mkConst bvSort "v"
  let f ← tm.mkConst funSort "f"
  solver.defineFunRec "f" #[] bvSort v |> assertError
    "recursive function definitions require a logic with quantifiers"
  solver.defineFunRecTerm f #[b, b] v |> assertError
    "recursive function definitions require a logic with quantifiers"

test![TestApiBlackSolver, defineFunRecGlobal] tm solver => do
  solver.push
  let bTrue ← tm.mkBoolean true
  -- `(define-fun f () Bool true)`
  let f ← solver.defineFunRec "f" #[] bool bTrue true
  let b ← tm.mkVar bool "b"
  -- `(define-fun g (b Boll) Bool b)`
  let g ← do
    let funSort ← tm.mkFunctionSort #[bool] bool
    solver.defineFunRecTerm (← tm.mkConst funSort "g") #[b] b true

  -- `(assert (or (not f) (not (g true))))`
  tm.mkTerm Kind.OR #[
    ← f.notTerm, ← (← tm.mkTerm Kind.APPLY_UF #[g, bTrue]).notTerm
  ] >>= solver.assertFormula
  assertTrue (← solver.checkSat).isUnsat
  solver.pop
  -- `(assert (or (not f) (not (g true))))`
  tm.mkTerm Kind.OR #[
    ← f.notTerm, ← (← tm.mkTerm Kind.APPLY_UF #[g, bTrue]).notTerm
  ] >>= solver.assertFormula
  assertTrue (← solver.checkSat).isUnsat

  let tm' ← TermManager.new
  let solver' ← Solver.new tm'
  let bool' ← tm'.getBooleanSort
  let b' ← tm'.mkVar bool' "b"
  let g ← tm.mkConst (← tm.mkFunctionSort #[bool] bool) "g"
  let g' ← tm'.mkConst (← tm'.mkFunctionSort #[bool'] bool') "g"
  -- the original test does not check anything about `solver'.defineFunRecTerm`, it just creates
  solver'.defineFunRecTerm g #[b'] b' true |> assertError
    "Given term is not associated with the term manager of this solver"
  solver'.defineFunRecTerm g' #[b] b true |> assertError
    "Given term is not associated with the term manager of this solver"

test![TestApiBlackSolver, defineFunsRec] tm solver => do
  let bvSort ← tm.mkBitVectorSort 32
  let funSort1 ← tm.mkFunctionSort #[bvSort, bvSort] bvSort
  let funSort2 ← tm.mkFunctionSort #[uninterpreted] int
  let b1 ← tm.mkVar bvSort "b1"
  let b11 ← tm.mkVar bvSort "b1"
  let b2 ← tm.mkVar int "b2"
  let b4 ← tm.mkVar uninterpreted "b4"
  let v1 ← tm.mkConst bvSort "v1"
  let v2 ← tm.mkConst int "v2"
  let v4 ← tm.mkConst uninterpreted "v4"
  let f1 ← tm.mkConst funSort1 "f1"
  let f2 ← tm.mkConst funSort2 "f2"
  let f3 ← tm.mkConst bvSort "f3"

  solver.defineFunsRec #[f1, f2] #[#[b1, b11], #[b4]] #[v1, v2] |> assertOkDiscard
  solver.defineFunsRec #[f1, f2] #[#[v1, b11], #[b4]] #[v1, v2] |> assertError
    "invalid bound variable in 'bvars' at index 0, expected a bound variable"
  solver.defineFunsRec #[f1, f3] #[#[b1, b11], #[b4]] #[v1, v2] |> assertError
    "invalid argument 'f3' for 'fun', expected function or nullary symbol"
  solver.defineFunsRec #[f1, f2] #[#[b1], #[b4]] #[v1, v2] |> assertError
    "invalid size of argument 'bvars', expected '2'"
  solver.defineFunsRec #[f1, f2] #[#[b1, b2], #[b4]] #[v1, v2] |> assertError
    "invalid sort of parameter in 'bvars' at index 1, expected sort '(_ BitVec 32)'"
  solver.defineFunsRec #[f1, f2] #[#[b1, b11], #[b4]] #[v1, v4] |> assertError
    "invalid sort of function body in 'terms' at index 1, expected 'Int'"

  let tm' ← TermManager.new
  let solver' ← Solver.new tm'
  let int' ← tm'.getIntegerSort
  let uSort2 ← tm'.mkUninterpretedSort "U"
  let bvSort2 ← tm'.mkBitVectorSort 32
  let funSort12 ← tm'.mkFunctionSort #[bvSort2, bvSort2] bvSort2
  let funSort22 ← tm'.mkFunctionSort #[uSort2] int'
  let b12 ← tm'.mkVar bvSort2 "b1"
  let b112 ← tm'.mkVar bvSort2 "b1"
  let b42 ← tm'.mkVar uSort2 "b4"
  let v12 ← tm'.mkConst bvSort2 "v1"
  let v22 ← tm'.mkConst int' "v2"
  let f12 ← tm'.mkConst funSort12 "f1"
  let f22 ← tm'.mkConst funSort22 "f2"
  solver'.defineFunsRec #[f12, f22] #[#[b12, b112], #[b42]] #[v12, v22] |> assertOk
  solver'.defineFunsRec #[f1, f22] #[#[b12, b112], #[b42]] #[v12, v22] |> assertError
    "invalid term in 'funs' at index 0, \
    expected a term associated with the term manager of this solver"
  solver'.defineFunsRec #[f12, f2] #[#[b12, b112], #[b42]] #[v12, v22] |> assertError
    "invalid term in 'funs' at index 1, \
    expected a term associated with the term manager of this solver"
  solver'.defineFunsRec #[f12, f22] #[#[b1, b112], #[b42]] #[v12, v22] |> assertError
    "invalid term in 'bvars' at index 0, \
    expected a term associated with the term manager of this solver"
  solver'.defineFunsRec #[f12, f22] #[#[b12, b11], #[b42]] #[v12, v22] |> assertError
    "invalid term in 'bvars' at index 1, \
    expected a term associated with the term manager of this solver"
  solver'.defineFunsRec #[f12, f22] #[#[b12, b112], #[b4]] #[v12, v22] |> assertError
    "invalid term in 'bvars' at index 0, \
    expected a term associated with the term manager of this solver"
  solver'.defineFunsRec #[f12, f22] #[#[b12, b112], #[b42]] #[v1, v22] |> assertError
    "invalid term in 'terms' at index 0, \
    expected a term associated with the term manager of this solver"
  solver'.defineFunsRec #[f12, f22] #[#[b12, b112], #[b42]] #[v12, v2] |> assertError
    "invalid term in 'terms' at index 1, \
    expected a term associated with the term manager of this solver"

test![TestApiBlackSolver, defineFunsRecWrongLogic] tm solver => do
  solver.setLogic "QF_BV"
  let bvSort ← tm.mkBitVectorSort 32
  let funSort1 ← tm.mkFunctionSort #[bvSort, bvSort] bvSort
  let funSort2 ← tm.mkFunctionSort #[uninterpreted] int
  let b ← tm.mkVar bvSort "b"
  let u ← tm.mkVar uninterpreted "u"
  let v1 ← tm.mkConst bvSort "v1"
  let v2 ← tm.mkConst int "v2"
  let f1 ← tm.mkConst funSort1 "f1"
  let f2 ← tm.mkConst funSort2 "f2"
  solver.defineFunsRec #[f1, f2] #[#[b, b], #[u]] #[v1, v2] |> assertError
    "recursive function definitions require a logic with quantifiers"

test![TestApiBlackSolver, defineFunsRecGlobal] tm solver => do
  let fSort ← tm.mkFunctionSort #[bool] bool

  solver.push
  let bTrue ← tm.mkBoolean true
  let b ← tm.mkVar bool "b"
  let gSym ← tm.mkConst fSort "g"
  -- `(define-funs-rec ((g ((b Bool)) Bool)) (b))`
  solver.defineFunsRec #[gSym] #[#[b]] #[b] true

  -- `(assert (not (g true)))`
  tm.mkTerm Kind.APPLY_UF #[gSym, bTrue] >>= Term.notTerm >>= solver.assertFormula
  assertTrue (← solver.checkSat).isUnsat
  solver.pop
  -- `(assert (not (g true)))`
  tm.mkTerm Kind.APPLY_UF #[gSym, bTrue] >>= Term.notTerm >>= solver.assertFormula
  assertTrue (← solver.checkSat).isUnsat

test![TestApiBlackSolver, defineFunsRecGlobal] tm solver => do
  let a ← tm.mkConst bool "a"
  let b ← tm.mkConst bool "b"
  solver.assertFormula a
  solver.assertFormula b
  let asserts := #[a, b]
  assertEq asserts (← solver.getAssertions)

test![TestApiBlackSolver, getInfo] tm solver => do
  solver.getInfo "name" |> assertOkDiscard
  solver.getInfo "asdf" |> assertError "unrecognized flag: asdf."

test![TestApiBlackSolver, getOption] tm solver => do
  solver.getOption "incremental" |> assertOkDiscard
  solver.getOption "asdf" |> assertError
    "Error in option parsing: Unrecognized option key or setting: asdf"

test![TestApiBlackSolver, getOptionNames] tm solver => do
  let names ← solver.getOptionNames
  assertTrue (100 < names.size)
  names.findIdx? (· == "verbose") |>.isSome |> assertTrue
  names.findIdx? (· == "foobar") |>.isSome |> assertFalse

-- test![TestApiBlackSolver, getOptionInfo] tm solver => do

test![TestApiBlackSolver, getUnsatAssumptions1] tm solver => do
  solver.setOption "incremental" "false"
  solver.checkSatAssuming #[(← tm.mkFalse)] |> assertOkDiscard
  solver.getUnsatAssumptions |> assertError
    "cannot get unsat assumptions unless explicitly enabled (try --produce-unsat-assumptions)"

test![TestApiBlackSolver, getUnsatAssumptions2] tm solver => do
  solver.setOption "incremental" "true"
  solver.setOption "produce-unsat-assumptions" "false"
  solver.checkSatAssuming #[(← tm.mkFalse)] |> assertOkDiscard
  solver.getUnsatAssumptions |> assertError
    "cannot get unsat assumptions unless explicitly enabled (try --produce-unsat-assumptions)"

test![TestApiBlackSolver, getUnsatAssumptions3] tm solver => do
  solver.setOption "incremental" "true"
  solver.setOption "produce-unsat-assumptions" "true"
  solver.checkSatAssuming #[(← tm.mkFalse)] |> assertOkDiscard
  solver.getUnsatAssumptions |> assertOkDiscard
  solver.checkSatAssuming #[(← tm.mkTrue)] |> assertOkDiscard
  solver.getUnsatAssumptions |> assertError "cannot get unsat assumptions unless in unsat mode."

test![TestApiBlackSolver, getUnsatCore1] tm solver => do
  solver.setOption "incremental" "false"
  solver.assertFormula (← tm.mkFalse)
  solver.checkSat |> assertOkDiscard
  solver.getUnsatCore |> assertError
    "cannot get unsat core unless explicitly enabled (try --produce-unsat-cores)"

test![TestApiBlackSolver, getUnsatCore2] tm solver => do
  solver.setOption "incremental" "true"
  solver.setOption "produce-unsat-cores" "false"
  solver.assertFormula (← tm.mkFalse)
  solver.checkSat |> assertOkDiscard
  solver.getUnsatCore |> assertError
    "cannot get unsat core unless explicitly enabled (try --produce-unsat-cores)"

test![TestApiBlackSolver, getUnsatCoreAndProof] tm solver => do
  solver.setOption "incremental" "true"
  solver.setOption "produce-unsat-cores" "true"
  solver.setOption "produce-proofs" "true"


  let uToIntSort ← tm.mkFunctionSort #[uninterpreted] int
  let intPredSort ← tm.mkFunctionSort #[int] bool

  let x ← tm.mkConst uninterpreted "x"
  let y ← tm.mkConst uninterpreted "y"
  let f ← tm.mkConst uToIntSort "f"
  let p ← tm.mkConst intPredSort "p"
  let zero ← tm.mkInteger 0
  let one ← tm.mkInteger 1
  let f_x ← tm.mkTerm Kind.APPLY_UF #[f, x]
  let f_y ← tm.mkTerm Kind.APPLY_UF #[f, y]
  let sum ← tm.mkTerm Kind.ADD #[f_x, f_y]
  let p_0 ← tm.mkTerm Kind.APPLY_UF #[p, zero]
  let p_f_y ← tm.mkTerm Kind.APPLY_UF #[p, f_y]
  tm.mkTerm Kind.GT #[zero, f_x] >>= solver.assertFormula
  tm.mkTerm Kind.GT #[zero, f_y] >>= solver.assertFormula
  tm.mkTerm Kind.GT #[sum, one] >>= solver.assertFormula
  solver.assertFormula p_0
  p_f_y.notTerm >>= solver.assertFormula
  assertTrue (← solver.checkSat).isUnsat

  let uc ← assertOk solver.getUnsatCore
  assertFalse uc.isEmpty

  solver.getProof |> assertOkDiscard
  solver.getProof ProofComponent.SAT |> assertOkDiscard

  solver.resetAssertions
  for t in uc do
    solver.assertFormula t
  let res ← solver.checkSat
  assertTrue res.isUnsat
  solver.getProof |> assertOkDiscard

test![TestApiBlackSolver, getUnsatCoreAndLemmas1] tm solver => do
  solver.setOption "produce-unsat-cores" "true"
  solver.setOption "unsat-cores-mode" "sat-proof"
  -- cannot ask before a check sat
  solver.getUnsatCoreLemmas |> assertError "cannot get unsat core unless in unsat mode."

  tm.mkFalse >>= solver.assertFormula
  assertTrue (← solver.checkSat).isUnsat
  solver.getUnsatCoreLemmas |> assertOkDiscard

test![TestApiBlackSolver, getUnsatCoreAndLemmas2] tm solver => do
  solver.setOption "incremental" "true"
  solver.setOption "produce-unsat-cores" "true"
  solver.setOption "produce-proofs" "true"


  let uToIntSort ← tm.mkFunctionSort #[uninterpreted] int
  let intPredSort ← tm.mkFunctionSort #[int] bool

  let x ← tm.mkConst uninterpreted "x"
  let y ← tm.mkConst uninterpreted "y"
  let f ← tm.mkConst uToIntSort "f"
  let p ← tm.mkConst intPredSort "p"
  let zero ← tm.mkInteger 0
  let one ← tm.mkInteger 1
  let f_x ← tm.mkTerm Kind.APPLY_UF #[f, x]
  let f_y ← tm.mkTerm Kind.APPLY_UF #[f, y]
  let sum ← tm.mkTerm Kind.ADD #[f_x, f_y]
  let p_0 ← tm.mkTerm Kind.APPLY_UF #[p, zero]
  let p_f_y ← tm.mkTerm Kind.APPLY_UF #[p, f_y]
  tm.mkTerm Kind.GT #[zero, f_x] >>= solver.assertFormula
  tm.mkTerm Kind.GT #[zero, f_y] >>= solver.assertFormula
  tm.mkTerm Kind.GT #[sum, one] >>= solver.assertFormula
  solver.assertFormula p_0
  p_f_y.notTerm >>= solver.assertFormula
  assertTrue (← solver.checkSat).isUnsat

  solver.getUnsatCoreLemmas |> assertOkDiscard

test![TestApiBlackSolver, getAbduct] tm solver => do
  solver.setLogic "QF_LIA"
  solver.setOption "produce-abducts" "true"
  solver.setOption "incremental" "false"

  let zero ← tm.mkInteger 0
  let x ← tm.mkConst int "x"
  let y ← tm.mkConst int "y"

  -- assumptions for abduction `x > 0`
  tm.mkTerm Kind.GT #[x, zero] >>= solver.assertFormula
  -- conjecture for abduction `y > 0`
  let conj ← tm.mkTerm Kind.GT #[y, zero]
  -- call the abduction api, while the resulting abduct is the output
  let output? ← solver.getAbduct conj
  -- we expect the resulting output to be a boolean formula
  let output ← assertSome output?
  assertTrue (← output.getSort).isBoolean

  -- try with a grammar, a simple grammar admitting true
  let truen ← tm.mkBoolean true
  let start ← tm.mkVar bool
  let mut g ← solver.mkGrammar #[] #[start]
  let conj2 ← tm.mkTerm Kind.GT #[x, zero]
  solver.getAbduct conj2 g |> assertError
    "invalid grammar, must have at least one rule for each non-terminal symbol"
  g ← g.addRule start truen
  -- call the abduction api, while the resulting abduct is the output
  let output2? ← solver.getAbduct conj2 g
  -- abduct must be true
  let output2 ← assertSome output2?
  assertEq truen output2

  let tm' ← TermManager.new
  let solver' ← Solver.new tm'
  solver'.setOption "produce-abducts" "true"
  let int' ← tm'.getIntegerSort
  let xx ← tm'.mkConst int' "x"
  let yy ← tm'.mkConst int' "y"
  let zzero ← tm'.mkInteger 0
  let sstart ← tm'.getBooleanSort >>= tm'.mkVar
  tm'.mkTerm Kind.GT #[← tm'.mkTerm Kind.ADD #[xx, yy], zzero] >>= solver'.assertFormula
  let mut gg ← solver'.mkGrammar #[] #[sstart]
  gg ← tm'.mkTrue >>= gg.addRule sstart
  let cconj2 ← tm'.mkTerm Kind.EQUAL #[zzero, zzero]
  solver'.getAbduct cconj2 gg |> assertOkDiscard
  solver'.getAbduct conj2 |> assertError
    "Given term is not associated with the term manager of this solver"
  solver'.getAbduct conj2 gg |> assertError
    "Given term is not associated with the term manager of this solver"
  solver'.getAbduct cconj2 g |> assertError
    "Given grammar is not associated with the term manager of this solver"

test![TestApiBlackSolver, getAbduct2] tm solver => do
  solver.setLogic "QF_LIA"
  solver.setOption "incremental" "false"
  let zero ← tm.mkInteger 0
  let x ← tm.mkConst int "x"
  let y ← tm.mkConst int "y"
  -- assumptions for abduction: `x > 0`
  tm.mkTerm Kind.GT #[x, zero] >>= solver.assertFormula
  -- conjecture for abduction: `y > 0`
  let conj ← tm.mkTerm Kind.GT #[y, zero]
  -- fails due to option not set
  solver.getAbduct conj |> assertError
    "cannot get abduct unless abducts are enabled (try --produce-abducts)"

test![TestApiBlackSolver, getAbductNext] tm solver => do
  solver.setLogic "QF_LIA"
  solver.setOption "produce-abducts" "true"
  solver.setOption "incremental" "true"

  let zero ← tm.mkInteger 0
  let x ← tm.mkConst int "x"
  let y ← tm.mkConst int "y"

  -- assumptions for abduction: `x > 0`
  tm.mkTerm Kind.GT #[x, zero] >>= solver.assertFormula
  -- conjecture for abduction: `y > 0`
  let conj ← tm.mkTerm Kind.GT #[y, zero]
  -- call the abduction api, while the resulting abduct is the output
  let output ← solver.getAbduct conj
  let output2 ← solver.getAbductNext
  -- should produce a different output
  assertNe output output2

test![TestApiBlackSolver, getInterpolant] tm solver => do
  solver.setLogic "QF_LIA"
  solver.setOption "produce-interpolants" "true"
  solver.setOption "incremental" "false"

  let zero ← tm.mkInteger 0
  let x ← tm.mkConst int "x"
  let y ← tm.mkConst int "y"
  let z ← tm.mkConst int "z"

  -- assumptions for interpolation: `x + y > 0 ∧ x < 0`
  tm.mkTerm Kind.GT #[← tm.mkTerm Kind.ADD #[x, y], zero] >>= solver.assertFormula
  tm.mkTerm Kind.LT #[x, zero] >>= solver.assertFormula
  -- conjecture for interpolation: `y + z > 0 ∨ z < 0`
  let conj ← tm.mkTerm Kind.OR #[
    ← tm.mkTerm Kind.GT #[← tm.mkTerm Kind.ADD #[y, z], zero],
    ← tm.mkTerm Kind.LT #[z, zero],
  ]
  -- call the interpolation api, while the resulting interpolant is the output
  let output? ← solver.getInterpolant conj
  -- we expect the resulting output to be a boolean formula
  let output ← assertSome output?
  assertTrue (← output.getSort).isBoolean

  -- try with a grammar, a simple grammar admitting true
  let truen ← tm.mkBoolean true
  let start ← tm.mkVar bool
  let mut g ← solver.mkGrammar #[] #[start]
  let conj2 ← tm.mkTerm Kind.EQUAL #[zero, zero]
  solver.getInterpolant conj2 g |> assertError
    "invalid grammar, must have at least one rule for each non-terminal symbol"
  g ← g.addRule start truen |> assertOk
  -- call the interpolation api, while the resulting interpolant is the output
  let output2? ← solver.getInterpolant conj2 g
  -- interpolant must be true
  let output2 ← assertSome output2?
  assertEq truen output2

  let tm' ← TermManager.new
  let solver' ← Solver.new tm'
  solver'.setOption "produce-interpolants" "true"
  let zzero ← tm'.mkInteger 0
  let sstart ← tm'.getBooleanSort >>= tm'.mkVar
  let mut gg ← solver'.mkGrammar #[] #[sstart]
  gg ← tm'.mkTrue >>= gg.addRule sstart
  let cconj2 ← tm'.mkTerm Kind.EQUAL #[zzero, zzero]
  solver'.getInterpolant cconj2 gg |> assertOkDiscard
  solver'.getInterpolant conj2 |> assertError
    "Given term is not associated with the term manager of this solver"
  solver'.getInterpolant conj2 gg |> assertError
    "Given term is not associated with the term manager of this solver"
  solver'.getInterpolant cconj2 g |> assertError
    "Given grammar is not associated with the term manager of this solver"

test![TestApiBlackSolver, getInterpolantNext] tm solver => do
  solver.setLogic "QF_LIA"
  solver.setOption "produce-interpolants" "true"
  solver.setOption "incremental" "true"

  let zero ← tm.mkInteger 0
  let x ← tm.mkConst int "x"
  let y ← tm.mkConst int "y"
  let z ← tm.mkConst int "z"
  -- assumptions for interpolation: `x + y > 0 ∧ x < 0`
  tm.mkTerm Kind.GT #[← tm.mkTerm Kind.ADD #[x, y], zero] >>= solver.assertFormula
  tm.mkTerm Kind.LT #[x, zero] >>= solver.assertFormula
  -- conjecture for interpolation: `y + z > 0 ∨ z < 0`
  let conj ← tm.mkTerm Kind.OR #[
    ← tm.mkTerm Kind.GT #[← tm.mkTerm Kind.ADD #[y, z], zero],
    ← tm.mkTerm Kind.LT #[z, zero],
  ]
  let output ← solver.getInterpolant conj
  let output2 ← solver.getInterpolantNext

  -- we expect the next output to be distinct
  assertNe output output2

test![TestApiBlackSolver, declarePool] tm solver => do
  let setSort ← tm.mkSetSort int
  let zero ← tm.mkInteger 0
  let x ← tm.mkConst int "x"
  let y ← tm.mkConst int "y"
  -- declare a ppol with initial value `{0, x, y}`
  let p ← solver.declarePool "p" int #[zero, x, y]
  -- pool should have the same sort
  assertTrue ((← p.getSort) == setSort)
  solver.declarePool "i" (Sort.null ()) #[] |> assertError "invalid null argument for 'sort'"

  let tm' ← TermManager.new
  let solver' ← Solver.new tm'
  let int' ← tm'.getIntegerSort
  let zero' ← tm'.mkInteger 0
  let x' ← tm'.mkConst int' "x"
  let y' ← tm'.mkConst int' "y"
  solver'.declarePool "p" int #[zero', x', y'] |> assertError
    "Given sort is not associated with the term manager of this solver"
  solver'.declarePool "p" int' #[zero, x', y'] |> assertError
    "invalid term in 'initValue' at index 0, \
    expected a term associated with the term manager of this solver"
  solver'.declarePool "p" int' #[zero', x, y'] |> assertError
    "invalid term in 'initValue' at index 1, \
    expected a term associated with the term manager of this solver"
  solver'.declarePool "p" int' #[zero', x', y] |> assertError
    "invalid term in 'initValue' at index 2, \
    expected a term associated with the term manager of this solver"

-- test![TestApiBlackSolver, getDriverOptions] tm solver => do

-- test![TestApiBlackSolver, getStatistics] tm solver => do

-- test![TestApiBlackSolver, printStatisticsSafe] tm solver => do

test![TestApiBlackSolver, getProofAndProofToString] tm solver => do
  solver.setOption "produce-proofs" "true"

  let uToIntSort ← tm.mkFunctionSort #[uninterpreted] int
  let intPredSort ← tm.mkFunctionSort #[int] bool

  let x ← tm.mkConst uninterpreted "x"
  let y ← tm.mkConst uninterpreted "y"
  let f ← tm.mkConst uToIntSort "f"
  let p ← tm.mkConst intPredSort "p"
  let zero ← tm.mkInteger 0
  let one ← tm.mkInteger 1
  let f_x ← tm.mkTerm Kind.APPLY_UF #[f, x]
  let f_y ← tm.mkTerm Kind.APPLY_UF #[f, y]
  let sum ← tm.mkTerm Kind.ADD #[f_x, f_y]
  let p_0 ← tm.mkTerm Kind.APPLY_UF #[p, zero]
  let p_f_y ← tm.mkTerm Kind.APPLY_UF #[p, f_y]
  tm.mkTerm Kind.GT #[zero, f_x] >>= solver.assertFormula
  tm.mkTerm Kind.GT #[zero, f_y] >>= solver.assertFormula
  tm.mkTerm Kind.GT #[sum, one] >>= solver.assertFormula
  solver.assertFormula p_0
  p_f_y.notTerm >>= solver.assertFormula
  assertTrue (← solver.checkSat).isUnsat

  let mut proofs ← solver.getProof |> assertOk
  assertFalse proofs.isEmpty
  let mut printedProof ← solver.proofToString proofs[0]! |> assertOk
  assertFalse printedProof.isEmpty
  printedProof ← solver.proofToString proofs[0]! ProofFormat.ALETHE |> assertOk
  assertFalse printedProof.isEmpty
  proofs ← solver.getProof ProofComponent.SAT |> assertOk
  printedProof ← solver.proofToString proofs[0]! ProofFormat.NONE |> assertOk
  assertFalse printedProof.isEmpty

-- test![TestApiBlackSolver, proofToStringAssertionNames] tm solver => do

-- test![TestApiBlackSolver, getDifficulty] tm solver => do
-- test![TestApiBlackSolver, getDifficulty2] tm solver => do
-- test![TestApiBlackSolver, getDifficulty3] tm solver => do

test![TestApiBlackSolver, getLearnedLiterals] tm solver => do
  solver.setOption "produce-learned-literals" "true"
  -- cannot ask before a check sat
  solver.getLearnedLiterals |> assertError
    "cannot get learned literals unless after a UNSAT, SAT or UNKNOWN response."
  solver.checkSat |> assertOkDiscard
  solver.getLearnedLiterals |> assertOkDiscard
  solver.getLearnedLiterals LearnedLitType.PREPROCESS |> assertOkDiscard

test![TestApiBlackSolver, getLearnedLiterals2] tm solver => do
  solver.setOption "produce-learned-literals" "true"
  let x ← tm.mkConst int "x"
  let y ← tm.mkConst int "y"
  let zero ← tm.mkInteger 0
  let ten ← tm.mkInteger 10
  let f0 ← tm.mkTerm Kind.GEQ #[x, ten]
  let f1 ← tm.mkTerm Kind.OR #[← tm.mkTerm Kind.GEQ #[zero, x], ← tm.mkTerm Kind.GEQ #[y, zero]]
  solver.assertFormula f0
  solver.assertFormula f1
  solver.checkSat |> assertOkDiscard
  solver.getLearnedLiterals |> assertOkDiscard

test![TestApiBlackSolver, getTimeoutCore] tm solver => do
  solver.setOption "timeout-core-timeout" "100"
  solver.setOption "produce-unsat-cores" "true"
  let x ← tm.mkConst int "x"
  let tt ← tm.mkBoolean true
  let hard ← tm.mkTerm Kind.EQUAL
    #[← tm.mkTerm Kind.MULT #[x, x], ← tm.mkIntegerOfString "501240912901901249014210220059591"]
  solver.assertFormula tt
  solver.assertFormula hard
  let (res, terms) ← solver.getTimeoutCore
  assertTrue res.isUnknown
  assertEq 1 terms.size
  assertEq hard terms[0]!

test![TestApiBlackSolver, getTimeoutCoreUnsat] tm solver => do
  solver.setOption "produce-unsat-cores" "true"
  let ff ← tm.mkBoolean false
  let tt ← tm.mkBoolean true
  solver.assertFormula tt
  solver.assertFormula ff
  solver.assertFormula tt
  let (res, terms) ← solver.getTimeoutCore
  assertTrue res.isUnsat
  assertEq 1 terms.size
  assertEq ff terms[0]!

test![TestApiBlackSolver, getTimeoutCoreAssuming] tm solver => do
  solver.setOption "produce-unsat-cores" "true"
  let ff ← tm.mkBoolean false
  let tt ← tm.mkBoolean true
  solver.assertFormula tt
  let (res, terms) ← solver.getTimeoutCoreAssuming #[ff, tt]
  assertTrue res.isUnsat
  assertEq 1 terms.size
  assertEq ff terms[0]!

test![TestApiBlackSolver, getTimeoutCoreAssumingEmpty] tm solver => do
  solver.setOption "produce-unsat-cores" "true"
  solver.getTimeoutCoreAssuming #[] |> assertError
    "cannot get timeout core assuming an empty set of assumptions"

test![TestApiBlackSolver, getValue1] tm solver => do
  solver.setOption "produce-models" "false"
  let t ← tm.mkTrue
  solver.assertFormula t
  solver.checkSat |> assertOkDiscard
  solver.getValue t |> assertError
    "cannot get value unless model generation is enabled (try --produce-models)"

test![TestApiBlackSolver, getValue2] tm solver => do
  solver.setOption "produce-models" "true"
  let t ← tm.mkFalse
  solver.assertFormula t
  solver.checkSat |> assertOkDiscard
  solver.getValue t |> assertError "cannot get value unless after a SAT or UNKNOWN response."

test![TestApiBlackSolver, getValue3] tm solver => do
  solver.setOption "produce-models" "true"
  let uToIntSort ← tm.mkFunctionSort #[uninterpreted] int
  let intPredSort ← tm.mkFunctionSort #[int] bool

  let x ← tm.mkConst uninterpreted "x"
  let y ← tm.mkConst uninterpreted "y"
  let z ← tm.mkConst uninterpreted "z"
  let f ← tm.mkConst uToIntSort "f"
  let p ← tm.mkConst intPredSort "p"
  let zero ← tm.mkInteger 0
  let one ← tm.mkInteger 1
  let f_x ← tm.mkTerm Kind.APPLY_UF #[f, x]
  let f_y ← tm.mkTerm Kind.APPLY_UF #[f, y]
  let sum ← tm.mkTerm Kind.ADD #[f_x, f_y]
  let p_0 ← tm.mkTerm Kind.APPLY_UF #[p, zero]
  let p_f_y ← tm.mkTerm Kind.APPLY_UF #[p, f_y]

  tm.mkTerm Kind.LEQ #[zero, f_x] >>= solver.assertFormula
  tm.mkTerm Kind.LEQ #[zero, f_y] >>= solver.assertFormula
  tm.mkTerm Kind.LEQ #[sum, one] >>= solver.assertFormula
  p_0.notTerm >>= solver.assertFormula
  solver.assertFormula p_f_y
  assertTrue (← solver.checkSat).isSat
  solver.getValue x |> assertOkDiscard
  solver.getValue y |> assertOkDiscard
  solver.getValue z |> assertOkDiscard
  solver.getValue sum |> assertOkDiscard
  solver.getValue p_f_y |> assertOkDiscard

  let a := #[← solver.getValue x, ← solver.getValue y, ← solver.getValue z]
  let b ← solver.getValues #[x, y, z]
  assertEq a b

  (← Solver.new tm).getValue x |> assertError
    "cannot get value unless model generation is enabled (try --produce-models)"

  let _ ← do
    let solver' ← Solver.new tm
    solver'.setOption "produce-models" "true"
    solver'.getValue x |> assertError
      "cannot get value unless after a SAT or UNKNOWN response."

  let _ ← do
    let solver' ← Solver.new tm
    solver'.setOption "produce-models" "true"
    solver'.checkSat |> assertOkDiscard
    solver'.getValue x |> assertOkDiscard

  let tm' ← TermManager.new
  let solver' ← Solver.new tm'
  solver'.setOption "produce-models" "true"
  solver'.checkSat |> assertOkDiscard
  solver'.getValue (← tm.mkConst bool "x") |> assertError
    "Given term is not associated with the term manager of this solver"

test![TestApiBlackSolver, getModelDomainElements] tm solver => do
  solver.setOption "produce-models" "true"
  let x ← tm.mkConst uninterpreted "x"
  let y ← tm.mkConst uninterpreted "y"
  let z ← tm.mkConst uninterpreted "z"
  let f ← tm.mkTerm Kind.DISTINCT #[x, y, z]
  solver.assertFormula f
  solver.checkSat |> assertOkDiscard
  let elems ← solver.getModelDomainElements uninterpreted
  assertEq 3 elems.size
  solver.getModelDomainElements int |> assertError
    "expected an uninterpreted sort as argument to getModelDomainElements."

test![TestApiBlackSolver, getModelDomainElements2] tm solver => do
  solver.setOption "produce-models" "true"
  solver.setOption "finite-model-find" "true"
  let x ← tm.mkVar uninterpreted "x"
  let y ← tm.mkVar uninterpreted "y"
  let eq ← tm.mkTerm Kind.EQUAL #[x, y]
  let bvl ← tm.mkTerm Kind.VARIABLE_LIST #[x, y]
  let f ← tm.mkTerm Kind.FORALL #[bvl, eq]
  solver.assertFormula f
  solver.checkSat |> assertOkDiscard
  let elems ← solver.getModelDomainElements uninterpreted
  -- a module for the above must interpret `u` as size 1
  assertEq 1 elems.size

test![TestApiBlackSolver, isModelCoreSymbol] tm solver => do
  solver.setOption "produce-models" "true"
  solver.setOption "model-cores" "simple"
  let x ← tm.mkConst uninterpreted "x"
  let y ← tm.mkConst uninterpreted "y"
  let z ← tm.mkConst uninterpreted "z"
  let zero ← tm.mkInteger 0
  let f ← tm.mkTerm Kind.NOT #[← tm.mkTerm Kind.EQUAL #[x, y]]
  solver.assertFormula f
  solver.checkSat |> assertOkDiscard
  assertTrue (← solver.isModelCoreSymbol x)
  assertTrue (← solver.isModelCoreSymbol y)
  assertFalse (← solver.isModelCoreSymbol z)
  solver.isModelCoreSymbol zero |> assertError
    "expected a free constant as argument to isModelCoreSymbol."

  let tm' ← TermManager.new
  let solver' ← Solver.new tm'
  solver'.setOption "produce-models" "true"
  solver'.checkSat |> assertOkDiscard
  solver'.isModelCoreSymbol (← tm.mkConst uninterpreted "x") |> assertError
    "Given term is not associated with the term manager of this solver"

test![TestApiBlackSolver, getModel] tm solver => do
  solver.setOption "produce-models" "true"
  let x ← tm.mkConst uninterpreted "x"
  let y ← tm.mkConst uninterpreted "y"
  -- -- not used in original test
  -- let z ← tm.mkConst uninterpreted "z"
  let f ← tm.mkTerm Kind.NOT #[← tm.mkTerm Kind.EQUAL #[x, y]]
  solver.assertFormula f
  solver.checkSat |> assertOkDiscard
  let sorts := #[uninterpreted]
  let terms := #[x, y]
  solver.getModel sorts terms |> assertOkDiscard
  solver.getModel sorts (terms.push <| Term.null ()) |> assertError
    "invalid null term in 'vars' at index 2"

test![TestApiBlackSolver, getModel2] tm solver => do
  solver.setOption "produce-models" "true"
  solver.getModel #[] #[] |> assertError
    "cannot get model unless after a SAT or UNKNOWN response."

test![TestApiBlackSolver, getModel3] tm solver => do
  solver.setOption "produce-models" "true"
  solver.checkSat |> assertOkDiscard
  solver.getModel #[] #[] |> assertOkDiscard
  solver.getModel #[int] #[] |> assertError
    "expected an uninterpreted sort as argument to getModel."

test![TestApiBlackSolver, getQuantifierElimitation] tm solver => do
  let x ← tm.mkVar bool "x"
  let term ← tm.mkTerm Kind.FORALL #[
    ← tm.mkTerm Kind.VARIABLE_LIST #[ x ],
    ← tm.mkTerm Kind.OR #[x, ← tm.mkTerm Kind.NOT #[ x ]]
  ]
  solver.getQuantifierElimination (Term.null ()) |> assertError "invalid null argument for 'q'"
  solver.getQuantifierElimination (← tm.mkBoolean false) |> assertError
    "Expecting a quantified formula as argument to get-qe."
  solver.getQuantifierElimination term |> assertOkDiscard

  let tm' ← TermManager.new
  let solver' ← Solver.new tm'
  solver'.checkSat |> assertOkDiscard
  solver'.getQuantifierElimination term |> assertError
    "Given term is not associated with the term manager of this solver"

test![TestApiBlackSolver, getQuantifierElimitationDisjunct] tm solver => do
  let x ← tm.mkVar bool "x"
  let term ← tm.mkTerm Kind.FORALL #[
    ← tm.mkTerm Kind.VARIABLE_LIST #[ x ],
    ← tm.mkTerm Kind.OR #[x, ← tm.mkTerm Kind.NOT #[ x ]]
  ]
  solver.getQuantifierEliminationDisjunct (Term.null ()) |> assertError
    "invalid null argument for 'q'"
  solver.getQuantifierEliminationDisjunct (← tm.mkBoolean false) |> assertError
    "Expecting a quantified formula as argument to get-qe."
  solver.getQuantifierEliminationDisjunct term |> assertOkDiscard

  let tm' ← TermManager.new
  let solver' ← Solver.new tm'
  solver'.checkSat |> assertOkDiscard
  solver'.getQuantifierEliminationDisjunct term |> assertError
    "Given term is not associated with the term manager of this solver"

test![TestApiBlackSolver, declareSepHeap] tm solver => do
  solver.setLogic "ALL"
  solver.setOption "incremental" "false"
  solver.declareSepHeap int int |> assertOk
  -- cannot declare separation logic heap more than once
  solver.declareSepHeap int int |> assertError
    "ERROR: cannot declare heap types for separation logic more than once.  \
    We are declaring heap of type Int -> Int, but we already have Int -> Int"

  let tm' ← TermManager.new
  let _ ← do
    let int' ← tm'.getIntegerSort
    let solver' ← Solver.new tm'
    -- no logic set yet
    solver'.declareSepHeap int' int' |> assertError
      "cannot call 'declareSepHeap()' if logic is not set"
  let _ ← do
    let real' ← tm'.getRealSort
    let solver' ← Solver.new tm'
    solver'.setLogic "ALL"
    solver'.declareSepHeap int real' |> assertError
      "Given sort is not associated with the term manager of this solver"
  let _ ← do
    let bool' ← tm'.getBooleanSort
    let solver' ← Solver.new tm'
    solver'.setLogic "ALL"
    solver'.declareSepHeap bool' int |> assertError
      "Given sort is not associated with the term manager of this solver"

/-- Helper function for `testGetSeparatior{Heap,Nil}TermX`.

Asserts and checks some simple separation logic constraints.
-/
def checkSimpleSeparationConstraints (tm : TermManager) (solver : Solver) : Env Unit := do
  let int ← tm.getIntegerSort
  -- declare the separation heap
  solver.declareSepHeap int int
  let x ← tm.mkConst int "x"
  let p ← tm.mkConst int "p"
  let heap ← tm.mkTerm Kind.SEP_PTO #[p, x]
  solver.assertFormula heap
  let nil ← tm.mkSepNil int
  tm.mkInteger 5 >>= nil.eqTerm >>= solver.assertFormula
  solver.checkSat |> assertOkDiscard

test![TestApiBlackSolver, getValueSepHeap1] tm solver => do
  solver.setLogic "QF_BV"
  solver.setOption "incremental" "false"
  solver.setOption "produce-models" "true"
  let t ← tm.mkTrue
  solver.assertFormula t
  solver.getValueSepHeap |> assertError
    "cannot obtain separation logic expressions if not using the separation logic theory."

test![TestApiBlackSolver, getValueSepHeap2] tm solver => do
  solver.setLogic "ALL"
  solver.setOption "incremental" "false"
  solver.setOption "produce-models" "false"
  checkSimpleSeparationConstraints tm solver
  solver.getValueSepHeap |> assertError
    "cannot get separation heap term unless model generation is enabled (try --produce-models)"

test![TestApiBlackSolver, getValueSepHeap3] tm solver => do
  solver.setLogic "ALL"
  solver.setOption "incremental" "false"
  solver.setOption "produce-models" "true"
  let t ← tm.mkFalse
  solver.assertFormula t
  solver.checkSat |> assertOkDiscard
  solver.getValueSepHeap |> assertError
    "can only get separtion heap term after SAT or UNKNOWN response."

test![TestApiBlackSolver, getValueSepHeap4] tm solver => do
  solver.setLogic "ALL"
  solver.setOption "incremental" "false"
  solver.setOption "produce-models" "true"
  let t ← tm.mkTrue
  solver.assertFormula t
  solver.checkSat |> assertOkDiscard
  solver.getValueSepHeap |> assertError "Failed to obtain heap/nil expressions from theory model."

test![TestApiBlackSolver, getValueSepHeap5] tm solver => do
  solver.setLogic "ALL"
  solver.setOption "incremental" "false"
  solver.setOption "produce-models" "true"
  checkSimpleSeparationConstraints tm solver
  solver.getValueSepHeap |> assertOkDiscard

test![TestApiBlackSolver, getValueSepNil1] tm solver => do
  solver.setLogic "QF_BV"
  solver.setOption "incremental" "false"
  solver.setOption "produce-models" "true"
  let t ← tm.mkTrue
  solver.assertFormula t
  solver.getValueSepNil |> assertError
    "cannot obtain separation logic expressions if not using the separation logic theory."

test![TestApiBlackSolver, getValueSepNil2] tm solver => do
  solver.setLogic "ALL"
  solver.setOption "incremental" "false"
  solver.setOption "produce-models" "false"
  checkSimpleSeparationConstraints tm solver
  solver.getValueSepNil |> assertError
    "cannot get separation nil term unless model generation is enabled (try --produce-models)"

test![TestApiBlackSolver, getValueSepNil3] tm solver => do
  solver.setLogic "ALL"
  solver.setOption "incremental" "false"
  solver.setOption "produce-models" "true"
  let t ← tm.mkFalse
  solver.assertFormula t
  solver.checkSat |> assertOkDiscard
  solver.getValueSepNil |> assertError
    "can only get separtion nil term after SAT or UNKNOWN response."

test![TestApiBlackSolver, getValueSepNil4] tm solver => do
  solver.setLogic "ALL"
  solver.setOption "incremental" "false"
  solver.setOption "produce-models" "true"
  let t ← tm.mkTrue
  solver.assertFormula t
  solver.checkSat |> assertOkDiscard
  solver.getValueSepNil |> assertError "Failed to obtain heap/nil expressions from theory model."

test![TestApiBlackSolver, getValueSepNil5] tm solver => do
  solver.setLogic "ALL"
  solver.setOption "incremental" "false"
  solver.setOption "produce-models" "true"
  checkSimpleSeparationConstraints tm solver
  solver.getValueSepNil |> assertOkDiscard

test![TestApiBlackSolver, push1] tm solver => do
  solver.setOption "incremental" "true"
  solver.push 1 |> assertOkDiscard
  solver.setOption "incremental" "false" |> assertError
    "invalid call to 'setOption' for option 'incremental', solver is already fully initialized"
  solver.setOption "incremental" "true" |> assertError
    "invalid call to 'setOption' for option 'incremental', solver is already fully initialized"

test![TestApiBlackSolver, push2] tm solver => do
  solver.setOption "incremental" "false"
  solver.push 1 |> assertError "cannot push when not solving incrementally (use --incremental)"

test![TestApiBlackSolver, pop1] tm solver => do
  solver.setOption "incremental" "false"
  solver.pop 1 |> assertError "cannot pop when not solving incrementally (use --incremental)"

test![TestApiBlackSolver, pop2] tm solver => do
  solver.setOption "incremental" "true"
  solver.pop 1 |> assertError "cannot pop beyond first pushed context"

test![TestApiBlackSolver, pop3] tm solver => do
  solver.setOption "incremental" "true"
  solver.push 1 |> assertOkDiscard
  solver.pop 1 |> assertOkDiscard
  solver.pop 1 |> assertError "cannot pop beyond first pushed context"

test![TestApiBlackSolver, blockModel1] tm solver => do
  let x ← tm.mkConst bool "x"
  x.eqTerm x >>= solver.assertFormula
  solver.checkSat |> assertOkDiscard
  solver.blockModel BlockModelsMode.LITERALS |> assertError
    "cannot get value unless model generation is enabled (try --produce-models)"

test![TestApiBlackSolver, blockModel2] tm solver => do
  solver.setOption "produce-models" "true"
  let x ← tm.mkConst bool "x"
  x.eqTerm x >>= solver.assertFormula
  solver.blockModel BlockModelsMode.LITERALS |> assertError
    "can only block model after SAT or UNKNOWN response."

test![TestApiBlackSolver, blockModel3] tm solver => do
  solver.setOption "produce-models" "true"
  let x ← tm.mkConst bool "x"
  x.eqTerm x >>= solver.assertFormula
  solver.checkSat |> assertOkDiscard
  solver.blockModel BlockModelsMode.LITERALS |> assertOkDiscard

test![TestApiBlackSolver, blockModelValues1] tm solver => do
  solver.setOption "produce-models" "true"
  let x ← tm.mkConst bool "x"
  x.eqTerm x >>= solver.assertFormula
  solver.checkSat |> assertOkDiscard
  solver.blockModelValues #[] |> assertError
    "invalid size of argument 'terms', expected a non-empty set of terms"
  solver.blockModelValues #[Term.null ()] |> assertError "invalid null term in 'terms' at index 0"
  solver.blockModelValues #[← tm.mkBoolean false] |> assertOkDiscard

  let tm' ← TermManager.new
  let solver' ← Solver.new tm'
  solver'.setOption "produce-models" "true"
  solver'.checkSat |> assertOkDiscard
  solver'.blockModelValues #[← tm.mkFalse] |> assertError
    "invalid term in 'terms' at index 0, \
    expected a term associated with the term manager of this solver"

test![TestApiBlackSolver, blockModelValues2] tm solver => do
  solver.setOption "produce-models" "true"
  let x ← tm.mkConst bool "x"
  x.eqTerm x >>= solver.assertFormula
  solver.checkSat |> assertOkDiscard
  solver.blockModelValues #[ x ] |> assertOkDiscard

test![TestApiBlackSolver, blockModelValues3] tm solver => do
  let x ← tm.mkConst bool "x"
  x.eqTerm x >>= solver.assertFormula
  solver.checkSat |> assertOkDiscard
  solver.blockModelValues #[ x ] |> assertError
    "cannot get value unless model generation is enabled (try --produce-models)"

test![TestApiBlackSolver, blockModelValues4] tm solver => do
  solver.setOption "produce-models" "true"
  let x ← tm.mkConst bool "x"
  x.eqTerm x >>= solver.assertFormula
  solver.blockModelValues #[ x ] |> assertError
    "can only block model values after SAT or UNKNOWN response."

test![TestApiBlackSolver, blockModelValues5] tm solver => do
  solver.setOption "produce-models" "true"
  let x ← tm.mkConst bool "x"
  x.eqTerm x >>= solver.assertFormula
  solver.checkSat |> assertOkDiscard
  solver.blockModelValues #[ x ] |> assertOkDiscard

test![TestApiBlackSolver, getInstantiations] tm solver => do
  let p ← solver.declareFun "p" #[int] bool
  let x ← tm.mkVar int "x"
  let bvl ← tm.mkTerm Kind.VARIABLE_LIST #[ x ]
  let app ← tm.mkTerm Kind.APPLY_UF #[p, x]
  let q ← tm.mkTerm Kind.FORALL #[bvl, app]
  solver.assertFormula q
  let five ← tm.mkInteger 5
  let app2 ← tm.mkTerm Kind.NOT #[← tm.mkTerm Kind.APPLY_UF #[p, five]]
  solver.assertFormula app2
  solver.getInstantiations |> assertError
    "cannot get instantiations unless after a UNSAT, SAT or UNKNOWN response."
  solver.checkSat |> assertOkDiscard
  solver.getInstantiations |> assertOkDiscard

test![TestApiBlackSolver, setInfo] tm solver => do
  let err s := s!"\
    unrecognized keyword: {s}, expected 'source', 'category', \
    'difficulty', 'filename', 'license', 'name', 'notes', 'smt-lib-version' or 'status'\
  "
  solver.setInfo "cvc5-lagic" "QF_BV" |> assertError (err "cvc5-lagic")
  solver.setInfo "cvc2-logic" "QF_BV" |> assertError (err "cvc2-logic")
  solver.setInfo "cvc5-logic" "asdf" |> assertError (err "cvc5-logic")

  let test (key val : String) : Env Unit := solver.setInfo key val |> assertOk

  let v := "asdf"
  test "source" v
  test "category" v
  test "difficulty" v
  test "filename" v
  test "license" v
  test "name" v
  test "notes" v

  test "smt-lib-version" "2"
  -- -- following two tests output garbage to `stderr`
  -- test "smt-lib-version" "2.0"
  -- test "smt-lib-version" "2.5"
  test "smt-lib-version" "2.6"
  solver.setInfo "smt-lib-version" ".0" |> assertError
    "invalid argument '.0' for 'value', expected '2.0', '2.5', '2.6', '2.7'"

  test "status" "sat"
  test "status" "unsat"
  test "status" "unknown"
  solver.setInfo "status" "asdf" |> assertError
    "invalid argument 'asdf' for 'value', expected 'sat', 'unsat' or 'unknown'"

test![TestApiBlackSolver, setLogic] tm solver => do
  solver.setLogic "AUFLIRA"
  solver.setLogic "AF_BV" |> assertError "invalid call to 'setLogic', logic is already set"
  tm.mkTrue >>= solver.assertFormula
  solver.setLogic "AUFLIRA" |> assertError "invalid call to 'setLogic', logic is already set"

test![TestApiBlackSolver, isLogicSet] tm solver => do
  assertFalse (← solver.isLogicSet)
  solver.setLogic "QF_BV"
  assertTrue (← solver.isLogicSet)

test![TestApiBlackSolver, getLogic] tm solver => do
  solver.getLogic |> assertError "invalid call to 'getLogic', logic has not yet been set"
  solver.setLogic "QF_BV"
  assertEq "QF_BV" (← solver.getLogic)

test![TestApiBlackSolver, setOption] tm solver => do
  solver.setOption "bv-sat-solver" "cadical" |> assertOkDiscard
  solver.setOption "bv-sat-solver" "1" |> assertError
    "Error in option parsing: unknown option for --bv-sat-solver: `1'.  Try --bv-sat-solver=help."
  tm.mkTrue >>= solver.assertFormula
  solver.setOption "bv-sat-solver" "cadical" |> assertError
    "invalid call to 'setOption' for option 'bv-sat-solver', solver is already fully initialized"

test![TestApiBlackSolver, resetAssertions] tm solver => do
  solver.setOption "incremental" "true" |> assertOkDiscard

  let bvSort ← tm.mkBitVectorSort 4
  let one ← tm.mkBitVector 4 1
  let x ← tm.mkConst bvSort "x"
  let ule ← tm.mkTerm Kind.BITVECTOR_ULE #[x, one]
  let srem ← tm.mkTerm Kind.BITVECTOR_SREM #[one, x]
  solver.push 4
  let slt ← tm.mkTerm Kind.BITVECTOR_SLT #[srem, one]
  solver.resetAssertions
  solver.checkSatAssuming #[slt, ule] |> assertOkDiscard

test![TestApiBlackSolver, declareSygusVar] tm solver => do
  solver.setOption "sygus" "true"
  let funSort ← tm.mkFunctionSort #[int] bool
  let nullSort := cvc5.Sort.null ()

  solver.declareSygusVar "" bool |> assertOkDiscard
  solver.declareSygusVar "" funSort |> assertOkDiscard
  solver.declareSygusVar "b" bool |> assertOkDiscard
  solver.declareSygusVar "" nullSort |> assertError
    "invalid null argument for 'sort'"
  solver.declareSygusVar "a" nullSort |> assertError
    "invalid null argument for 'sort'"

  (← Solver.new tm).declareSygusVar "" bool |> assertError
    "cannot call declareSygusVar unless sygus is enabled (use --sygus)"

  let tm' ← TermManager.new
  let solver' ← Solver.new tm'
  solver'.setOption "sygus" "true"
  solver'.declareSygusVar "" bool |> assertError
    "Given sort is not associated with the term manager of this solver"

test![TestApiBlackSolver, mkGrammar] tm solver => do
  let nullTerm := Term.null ()
  let boolTerm ← tm.mkBoolean true
  let boolVar ← tm.mkVar bool
  let intVar ← tm.mkVar int

  solver.mkGrammar #[] #[intVar] |> assertOkDiscard
  solver.mkGrammar #[boolVar] #[intVar] |> assertOkDiscard
  solver.mkGrammar #[] #[] |> assertError
    "invalid size of argument 'ntSymbols', expected a non-empty vector"
  solver.mkGrammar #[] #[nullTerm] |> assertError
    "invalid null term in 'ntSymbols' at index 0"
  solver.mkGrammar #[] #[boolTerm] |> assertError
    "invalid bound variable in 'ntSymbols' at index 0, expected a bound variable"
  solver.mkGrammar #[boolTerm] #[intVar] |> assertError
    "invalid bound variable in 'boundVars' at index 0, expected a bound variable"

  let tm' ← TermManager.new
  let solver' ← Solver.new tm'
  let boolVar' ← tm'.mkVar (← tm'.getBooleanSort)
  let intVar' ← tm'.mkVar (← tm'.getIntegerSort)
  solver'.mkGrammar #[boolVar'] #[intVar'] |> assertOkDiscard
  solver'.mkGrammar #[boolVar] #[intVar'] |> assertError
    "invalid term in 'boundVars' at index 0, \
    expected a term associated with the term manager of this solver"
  solver'.mkGrammar #[boolVar'] #[intVar] |> assertError
    "invalid term in 'ntSymbols' at index 0, \
    expected a term associated with the term manager of this solver"

test![TestApiBlackSolver, synthFun] tm solver => do
  solver.setOption "sygus" "true"
  let fls ← tm.mkBoolean false
  let nullTerm := Term.null ()
  let term ← tm.mkVar bool "term"
  let start1 ← tm.mkVar bool "start1"
  let start2 ← tm.mkVar int "start2"

  let mut g1 ← solver.mkGrammar #[term] #[start1]
  solver.synthFun "" #[] bool |> assertOkDiscard
  solver.synthFun "f1" #[term] bool |> assertOkDiscard
  solver.synthFun "f2" #[term] bool g1 |> assertError
    "invalid grammar, must have at least one rule for each non-terminal symbol"
  g1 ← g1.addRule start1 fls

  let mut g2 ← solver.mkGrammar #[term] #[start2]
  g2 ← g2.addRule start2 (← tm.mkInteger 0)

  solver.synthFun "" #[] bool |> assertOkDiscard
  solver.synthFun "f1" #[term] bool |> assertOkDiscard
  solver.synthFun "f2" #[term] bool g1 |> assertOkDiscard

  solver.synthFun "f3" #[nullTerm] bool |> assertError
    "invalid null term in 'boundVars' at index 0"
  solver.synthFun "f4" #[term] (Sort.null ()) |> assertError
    "invalid null argument for 'sort'"
  solver.synthFun "f6" #[term] bool g2 |> assertError
    "invalid Start symbol for grammar, expected Start's sort to be Bool but found Int"

  let tm2 ← TermManager.new
  let solver2 ← Solver.new tm2
  solver2.setOption "sygus" "true"
  let bool2 ← tm2.getBooleanSort
  let term2 ← tm2.mkVar bool2 "term2"
  solver2.synthFun "f1" #[term2] bool |> assertError
    "Given sort is not associated with the term manager of this solver"
  solver2.synthFun "" #[] bool |> assertError
    "Given sort is not associated with the term manager of this solver"
  solver2.synthFun "f1" #[term] bool2 |> assertError
    "invalid term in 'boundVars' at index 0, \
    expected a term associated with the term manager of this solver"

test![TestApiBlackSolver, addSygusConstraint] tm solver => do
  solver.setOption "sygus" "true"
  let nullTerm := Term.null ()
  let boolTerm ← tm.mkBoolean true
  let intTerm ← tm.mkInteger 1

  solver.addSygusConstraint boolTerm |> assertOk
  solver.addSygusConstraint nullTerm |> assertError
    "invalid null argument for 'term'"
  solver.addSygusConstraint intTerm |> assertError
    "invalid argument '1' for 'term', expected boolean term"

  let tm2 ← TermManager.new
  let solver2 ← Solver.new tm2
  solver2.setOption "sygus" "true"
  solver2.addSygusConstraint boolTerm |> assertError
    "Given term is not associated with the term manager of this solver"

test![TestApiBlackSolver, getSygusConstraints] tm solver => do
  solver.setOption "sygus" "true"
  let tru ← tm.mkBoolean true
  let fls ← tm.mkBoolean false
  solver.addSygusConstraint tru
  solver.addSygusConstraint fls
  assertEq (← solver.getSygusConstraints) #[tru, fls]

test![TestApiBlackSolver, addSygusAssume] tm solver => do
  solver.setOption "sygus" "true"
  let nullTerm := Term.null ()
  let boolTerm ← tm.mkBoolean true
  let intTerm ← tm.mkInteger 1

  solver.addSygusAssume boolTerm |> assertOk
  solver.addSygusAssume nullTerm |> assertError
    "invalid null argument for 'term'"
  solver.addSygusAssume intTerm |> assertError
    "invalid argument '1' for 'term', expected boolean term"

  let tm2 ← TermManager.new
  let solver2 ← Solver.new tm2
  solver2.setOption "sygus" "true"
  solver2.addSygusAssume boolTerm |> assertError
    "Given term is not associated with the term manager of this solver"

test![TestApiBlackSolver, getSygusAssumptions] tm solver => do
  solver.setOption "sygus" "true"
  let tru ← tm.mkBoolean true
  let fls ← tm.mkBoolean false
  solver.addSygusAssume tru
  solver.addSygusAssume fls
  assertEq (← solver.getSygusAssumptions) #[tru, fls]

test![TestApiBlackSolver, addSygusInvConstraint] tm solver => do
  solver.setOption "sygus" "true"
  let nullTerm := Term.null ()
  let intTerm ← tm.mkInteger 1
  let real ← tm.getRealSort

  let inv ← solver.declareFun "inv" #[real] bool
  let pre ← solver.declareFun "pre" #[real] bool
  let trans ← solver.declareFun "trans" #[real, real] bool
  let post ← solver.declareFun "trans" #[real] bool

  let inv1 ← solver.declareFun "inv1" #[real] real

  let trans1 ← solver.declareFun "trans1" #[bool, real] bool
  let trans2 ← solver.declareFun "trans2" #[real, bool] bool
  let trans3 ← solver.declareFun "trans3" #[real, real] real

  solver.addSygusInvConstraint inv pre trans post |> assertOk

  solver.addSygusInvConstraint nullTerm pre trans post |> assertError
    "invalid null argument for 'inv'"
  solver.addSygusInvConstraint inv nullTerm trans post |> assertError
    "invalid null argument for 'pre'"
  solver.addSygusInvConstraint inv pre nullTerm post |> assertError
    "invalid null argument for 'trans'"
  solver.addSygusInvConstraint inv pre trans nullTerm |> assertError
    "invalid null argument for 'post'"

  solver.addSygusInvConstraint inv1 pre trans post |> assertError
    "invalid argument 'inv1' for 'inv', expected boolean range"

  solver.addSygusInvConstraint inv trans trans post |> assertError
    "expected inv and pre to have the same sort"

  solver.addSygusInvConstraint inv pre intTerm post |> assertError
    "expected the sort of trans sort to be (-> Real Bool)"
  solver.addSygusInvConstraint inv pre pre post |> assertError
    "expected the sort of trans sort to be (-> Real Bool)"
  solver.addSygusInvConstraint inv pre trans1 post |> assertError
    "expected the sort of trans sort to be (-> Real Bool)"
  solver.addSygusInvConstraint inv pre trans2 post |> assertError
    "expected the sort of trans sort to be (-> Real Bool)"
  solver.addSygusInvConstraint inv pre trans3 post |> assertError
    "expected the sort of trans sort to be (-> Real Bool)"

  solver.addSygusInvConstraint inv pre trans trans |> assertError
    "expected inv and post to have the same sort"

  let tm' ← TermManager.new
  let solver' ← Solver.new tm'
  solver'.setOption "sygus" "true"
  let bool' ← tm'.getBooleanSort
  let real' ← tm'.getRealSort
  let inv' ← solver'.declareFun "inv" #[real'] bool'
  let pre' ← solver'.declareFun "inv" #[real'] bool'
  let trans' ← solver'.declareFun "inv" #[real', real'] bool'
  let post' ← solver'.declareFun "inv" #[real'] bool'
  solver'.addSygusInvConstraint inv' pre' trans' post' |> assertOk
  solver'.addSygusInvConstraint inv pre' trans' post' |> assertError
    "Given term is not associated with the term manager of this solver"
  solver'.addSygusInvConstraint inv' pre trans' post' |> assertError
    "Given term is not associated with the term manager of this solver"
  solver'.addSygusInvConstraint inv' pre' trans post' |> assertError
    "Given term is not associated with the term manager of this solver"
  solver'.addSygusInvConstraint inv' pre' trans' post |> assertError
    "Given term is not associated with the term manager of this solver"

test![TestApiBlackSolver, checkSynth] tm solver => do
  solver.setOption "sygus" "true"
  solver.checkSynth |> assertOkDiscard

test![TestApiBlackSolver, getSynthSolution] tm solver => do
  solver.setOption "sygus" "true"
  solver.setOption "incremental" "false"

  let nullTerm := Term.null ()
  let fls ← tm.mkBoolean false
  let f ← solver.synthFun "f" #[] bool

  solver.getSynthSolution f |> assertError
    "solver is not in a state immediately preceded by a successful call to checkSynth"

  let synthRes ← solver.checkSynth
  assertTrue synthRes.hasSolution

  solver.getSynthSolution f |> assertOkDiscard
  solver.getSynthSolution f |> assertOkDiscard

  solver.getSynthSolution nullTerm |> assertError
    "invalid null argument for 'term'"
  solver.getSynthSolution fls |> assertError
    "synthesis solution not found for given term"

  (← Solver.new tm).getSynthSolution f |> assertError
    "solver is not in a state immediately preceded by a successful call to checkSynth"

test![TestApiBlackSolver, getSynthSolutions] tm solver => do
  solver.setOption "sygus" "true"
  solver.setOption "incremental" "false"

  let nullTerm := Term.null ()
  let fls ← tm.mkBoolean false
  let f ← solver.synthFun "f" #[] bool

  solver.getSynthSolutions #[] |> assertError
    "invalid size of argument 'terms', expected non-empty vector"
  solver.getSynthSolutions #[f] |> assertError
    "solver is not in a state immediately preceded by a successful call to checkSynth"

  let synthRes ← solver.checkSynth
  assertTrue synthRes.hasSolution

  solver.getSynthSolutions #[f] |> assertOkDiscard
  solver.getSynthSolutions #[f] |> assertOkDiscard

  solver.getSynthSolutions #[] |> assertError
    "invalid size of argument 'terms', expected non-empty vector"
  solver.getSynthSolutions #[nullTerm] |> assertError
    "invalid null term in 'terms' at index 0"
  solver.getSynthSolutions #[fls] |> assertError
    "synthesis solution not found for term at index 0"

  (← Solver.new tm).getSynthSolutions #[f] |> assertError
    "solver is not in a state immediately preceded by a successful call to checkSynth"

test![TestApiBlackSolver, checkSynthNext] tm solver => do
  solver.setOption "sygus" "true"
  solver.setOption "incremental" "true"
  let f ← solver.synthFun "f" #[] bool

  let synthRes ← solver.checkSynth
  assertTrue synthRes.hasSolution
  solver.getSynthSolutions #[f] |> assertOkDiscard
  let synthRes ← solver.checkSynthNext
  assertTrue synthRes.hasSolution
  solver.getSynthSolutions #[f] |> assertOkDiscard

test![TestApiBlackSolver, checkSynthNext2] tm solver => do
  solver.setOption "sygus" "true"
  solver.setOption "incremental" "false"
  let _f ← solver.synthFun "f" #[] bool
  solver.checkSynth |> assertOkDiscard
  solver.checkSynthNext |> assertError
    "cannot check for a next synthesis solution when not solving incrementally (use --incremental)"

test![TestApiBlackSolver, checkSynthNext3] tm solver => do
  solver.setOption "sygus" "true"
  solver.setOption "incremental" "true"
  let _f ← solver.synthFun "f" #[] bool
  solver.checkSynthNext |> assertError
    "Cannot check-synth-next unless immediately preceded \
    by a successful call to check-synth(-next)."

test![TestApiBlackSolver, findSynth] tm solver => do
  solver.setOption "sygus" "true"
  let start ← tm.mkVar bool
  let mut grammar ← solver.mkGrammar #[] #[start]
  solver.synthFun "f" #[] bool grammar |> assertError
    "invalid grammar, must have at least one rule for each non-terminal symbol"

  let tru ← tm.mkBoolean true
  let fls ← tm.mkBoolean false
  grammar ← grammar.addRule start tru
  grammar ← grammar.addRule start fls
  let _f ← solver.synthFun "f" #[] bool grammar

  -- should enumerate based on the grammar of the function to synthesize above
  let term ← solver.findSynth .ENUM
  assertFalse term.isNull
  assertTrue (← term.getSort).isBoolean

test![TestApiBlackSolver, findSynth2] tm solver => do
  solver.setOption "sygus" "true"
  solver.setOption "incremental" "true"
  let start ← tm.mkVar bool
  let mut grammar ← solver.mkGrammar #[] #[start]
  let tru ← tm.mkBoolean true
  let fls ← tm.mkBoolean false
  grammar ← grammar.addRule start tru
  grammar ← grammar.addRule start fls

  -- should enumerate true/false
  let term ← solver.findSynth .ENUM grammar
  assertFalse term.isNull
  assertTrue (← term.getSort).isBoolean
  let term ← solver.findSynthNext
  assertFalse term.isNull
  assertTrue (← term.getSort).isBoolean

test![TestApiBlackSolver, tupleProject] tm solver => do
  let elements := #[
    ← tm.mkBoolean true, ← tm.mkInteger 3, ← tm.mkString "C",
    ← tm.mkTerm Kind.SET_SINGLETON #[← tm.mkString "Z"],
  ]

  let tuple ← tm.mkTuple elements

  let indices1 := #[]
  let indices2 := #[0]
  let indices3 := #[0, 1]
  let indices4 := #[0, 0, 2, 2, 3, 3, 0]
  let indices5 := #[4]
  let indices6 := #[0, 4]

  tm.mkTermOfOp (← tm.mkOp Kind.TUPLE_PROJECT indices1) #[tuple] |> assertOkDiscard
  tm.mkTermOfOp (← tm.mkOp Kind.TUPLE_PROJECT indices2) #[tuple] |> assertOkDiscard
  tm.mkTermOfOp (← tm.mkOp Kind.TUPLE_PROJECT indices3) #[tuple] |> assertOkDiscard
  tm.mkTermOfOp (← tm.mkOp Kind.TUPLE_PROJECT indices4) #[tuple] |> assertOkDiscard

  tm.mkTermOfOp (← tm.mkOp Kind.TUPLE_PROJECT indices5) #[tuple] |> assertError
    "Project index 4 in term \
    ((_ tuple.project 4) (tuple true 3 \"C\" (set.singleton \"Z\"))) is >= 4 \
    which is the length of tuple (tuple true 3 \"C\" (set.singleton \"Z\"))\n"
  tm.mkTermOfOp (← tm.mkOp Kind.TUPLE_PROJECT indices6) #[tuple] |> assertError
    "Project index 4 in term \
    ((_ tuple.project 0 4) (tuple true 3 \"C\" (set.singleton \"Z\"))) is >= 4 \
    which is the length of tuple (tuple true 3 \"C\" (set.singleton \"Z\"))\n"

  let indices := #[0, 3, 2, 0, 1, 2]

  let op ← tm.mkOp Kind.TUPLE_PROJECT indices
  let projection ← tm.mkTermOfOp op #[tuple]

  let datatype ← (← tuple.getSort).getDatatype
  let constructor := datatype[0]!

  for index in indices do
    let selectorTerm ← constructor[index]!.getTerm
    let selectedTerm ← tm.mkTerm Kind.APPLY_SELECTOR #[selectorTerm, tuple]
    let simplifiedTerm ← solver.simplify selectedTerm
    assertEq elements[index]! simplifiedTerm

  projection.toString
  |> assertEq "((_ tuple.project 0 3 2 0 1 2) (tuple true 3 \"C\" (set.singleton \"Z\")))"

-- test![TestApiBlackSolver, output] tm solver => do

test![TestApiBlackSolver, getDatatypeArity] tm solver => do
  let ctor1 ← tm.mkDatatypeConstructorDecl "_x21"
  let ctor2 ← tm.mkDatatypeConstructorDecl "_x31"
  let s3 ← solver.declareDatatype "_x17" #[ctor1, ctor2]
  assertEq 0 (← s3.getDatatypeArity)

test![TestApiBlackSolver, declareOracleFunError] tm solver => do
  -- cannot declare without option
  solver.declareOracleFun "f" #[int] int (fun _input => tm.mkInteger 0) |> assertError
    "cannot call declareOracleFun unless oracles is enabled (use --oracles)"
  solver.setOption "oracles" "true"
  let nullSort := Sort.null ()
  -- -- bad sort
  solver.declareOracleFun "f" #[nullSort] int (fun _input => tm.mkInteger 0) |> assertError
    "invalid null domain sort in 'sorts' at index 0"

test![TestApiBlackSolver, declareOracleFunUnsat] tm solver => do
  solver.setOption "oracles" "true"
  let oracle (terms : Array Term) : Env Term := do
    if let some term := terms[0]? then
      if let some val := term.getUInt32Value? then
        return ← val.toNat.succ |> Int.ofNat |> tm.mkInteger
    tm.mkInteger 0
  -- `f` is the function implementing `(lambda ((x Int)) (+ x 1))`
  let f ← solver.declareOracleFun "f" #[int] int oracle
  let three ← tm.mkInteger 3
  let five ← tm.mkInteger 5
  let eq ← tm.mkTerm Kind.EQUAL #[← tm.mkTerm Kind.APPLY_UF #[f, three], five]
  solver.assertFormula eq
  -- `(f 3) = 5`
  assertTrue (← solver.checkSat).isUnsat

  let tm' ← TermManager.new
  let solver' ← Solver.new tm'
  solver'.setOption "oracles" "true"
  let int' ← tm'.getIntegerSort
  let oracle' (terms : Array Term) : Env Term := do
    if let some term := terms[0]? then
      if let some val := term.getUInt32Value? then
        return ← val.toNat.succ |> Int.ofNat |> tm'.mkInteger
    tm'.mkInteger 0
  solver'.declareOracleFun "f" #[int'] int oracle' |> assertError
    "Given sort is not associated with the term manager of this solver"
  solver'.declareOracleFun "f" #[int] int' oracle' |> assertError
    "invalid domain sort in 'sorts' at index 0, \
    expected a sort associated with the term manager of this solver object"

  -- this cannot be caught during declaration, is caught during check-sat
  let f2 ← solver'.declareOracleFun "f2" #[int'] int' oracle
  let eq2 ← tm'.mkTerm Kind.EQUAL #[
    ← tm'.mkTerm Kind.APPLY_UF #[f2, ← tm'.mkInteger 3], ← tm'.mkInteger 5
  ]
  solver'.assertFormula eq2
  solver'.checkSat |> assertError
    "Evaluated an oracle call that is not associated with the term manager of this solver"

  -- added from the original test to check we're handling nested errors properly
  let tm'' ← TermManager.new
  let solver'' ← Solver.new tm''
  solver''.setOption "oracles" "true"
  let int'' ← tm''.getIntegerSort
  let f3 ← solver''.declareOracleFun "f3" #[int''] int''
    fun _ => throw (Error.error "internal failure")
  let eq3 ← tm''.mkTerm Kind.EQUAL #[
    ← tm''.mkTerm Kind.APPLY_UF #[f3, ← tm''.mkInteger 3], ← tm''.mkInteger 5
  ]
  solver''.assertFormula eq3
  solver''.checkSat |> assertError "internal failure"

test![TestApiBlackSolver, declareOracleFunSat] tm solver => do
  let int ← tm.getIntegerSort
  solver.setOption "oracles" "true"
  solver.setOption "produce-models" "true"
  -- `f` is the function implementing `(lambda ((x Int)) (% x 10))`
  let f ← solver.declareOracleFun "f" #[int] int fun terms => do
    if let some term := terms[0]? then
      if let some val := term.getUInt32Value? then
        return ← tm.mkInteger (val.toNat % 10)
    tm.mkInteger 0
  let seven ← tm.mkInteger 7
  let x ← tm.mkConst int "x"
  let lb ← tm.mkTerm Kind.GEQ #[x, ← tm.mkInteger 0]
  solver.assertFormula lb
  let ub ← tm.mkTerm Kind.LEQ #[x, ← tm.mkInteger 100]
  solver.assertFormula ub
  let eq ← tm.mkTerm Kind.EQUAL #[← tm.mkTerm Kind.APPLY_UF #[f, x], seven]
  solver.assertFormula eq
  -- `x ≥ 0 ∧ x ≤ 100 ∧ (f x) = 7`
  assertTrue (← solver.checkSat).isSat
  let xval ← solver.getValue x
  assertTrue xval.isUInt32Value
  assertEq 7 (xval.getUInt32Value!.toNat % 10)

test![TestApiBlackSolver, declareOracleFunSat2] tm solver => do
  solver.setOption "oracles" "true"
  solver.setOption "produce-models" "true"
  -- `eq` is the function implementing `(lambda ((x Int) (y Int)) (= x y))`
  let eq ← solver.declareOracleFun "eq" #[int, int] bool fun terms => do
    if let some t1 := terms[0]? then
      if let some t2 := terms[1]? then
        return ← tm.mkBoolean (t1 == t2)
    throw (Error.error "expected exactly two terms")
  let x ← tm.mkConst int "x"
  let y ← tm.mkConst int "y"
  let neq ← tm.mkTerm Kind.NOT #[← tm.mkTerm Kind.APPLY_UF #[eq, x, y]]
  solver.assertFormula neq
  -- `(not (eq x y))`
  assertTrue (← solver.checkSat).isSat
  let xval ← solver.getValue x
  let yval ← solver.getValue y
  assertNe xval yval

-- #TODO `Plugin`-related functions not implemented
-- test![TestApiBlackSolver, pluginUnsat] tm solver => do
-- test![TestApiBlackSolver, pluginListen] tm solver => do
-- test![TestApiBlackSolver, pluginListenCadical] tm solver => do

test![TestApiBlackSolver, verticalBars] tm solver => do
  let a ← solver.declareFun "|a |" #[] real
  assertEq "|a |" a.toString

test![TestApiBlackSolver, getVersion] tm solver => do
  solver.getVersion |> assertOkDiscard

test![TestApiBlackSolver, multipleSolvers] tm _solver => do
  let (value1, zero, definedFunction) ← do
    let s1 ← Solver.new tm
    s1.setLogic "ALL"
    s1.setOption "produce-models" "true"
    let f1 ← s1.declareFun "f1" #[] int
    let x ← tm.mkVar int "x"
    let zero ← tm.mkInteger 0
    let definedFunction ← s1.defineFun "f" #[ x ] int zero
    f1.eqTerm zero >>= s1.assertFormula
    s1.checkSat |> assertOkDiscard
    let value1 ← s1.getValue f1
    pure (value1, zero, definedFunction)
  assertEq zero value1
  let value2 ← do
    let s2 ← Solver.new tm
    s2.setLogic "ALL"
    s2.setOption "produce-models" "true"
    let f2 ← s2.declareFun "f2" #[] int
    f2.eqTerm value1 >>= s2.assertFormula
    s2.checkSat |> assertOkDiscard
    s2.getValue f2
  assertEq value1 value2
  let value3 ← do
    let s3 ← Solver.new tm
    s3.setLogic "ALL"
    s3.setOption "produce-models" "true"
    let f3 ← s3.declareFun "f3" #[] int
    let apply ← tm.mkTerm Kind.APPLY_UF #[definedFunction, zero]
    f3.eqTerm apply >>= s3.assertFormula
    s3.checkSat |> assertOkDiscard
    s3.getValue f3
  assertEq value1 value3

test![TestApiBlackSolver, basicFiniteField] tm solver => do
  solver.setOption "produce-models" "true"

  let F ← tm.mkFiniteFieldSort 5
  let a ← tm.mkConst F "a"
  let b ← tm.mkConst F "b"
  assertEq 5 F.getFiniteFieldSize!

  let inv ← tm.mkTerm Kind.EQUAL
    #[← tm.mkTerm Kind.FINITE_FIELD_MULT #[a, b], ← tm.mkFiniteFieldElem 1 F]
  let aIsTwo ← tm.mkTerm Kind.EQUAL #[a, ← tm.mkFiniteFieldElem 2 F]

  solver.assertFormula inv
  solver.assertFormula aIsTwo
  -- -- #TODO requires a cvc5 dyn-lib with *cocoa* linked
  -- assertTrue (← solver.checkSat).isSat
  -- assertEq 2 (← solver.getValue a).getFiniteFieldValue!
  -- assertEq (-2) (← solver.getValue b).getFiniteFieldValue!

  let bIsTwo ← tm.mkTerm Kind.EQUAL #[b, ← tm.mkFiniteFieldElem 2 F]
  solver.assertFormula bIsTwo
  -- -- #TODO requires a cvc5 dyn-lib with *cocoa* linked
  -- assertFalse (← solver.checkSat).isSat

test![TestApiBlackSolver, basicFiniteField] tm solver => do
  solver.setOption "produce-models" "true"

  let F ← tm.mkFiniteFieldSortOfString "101" 2
  let a ← tm.mkConst F "a"
  let b ← tm.mkConst F "b"
  assertEq 5 F.getFiniteFieldSize!

  let inv ← tm.mkTerm Kind.EQUAL
    #[← tm.mkTerm Kind.FINITE_FIELD_MULT #[a, b], ← tm.mkFiniteFieldElemOfString "1" F 3]
  let aIsTwo ← tm.mkTerm Kind.EQUAL #[a, ← tm.mkFiniteFieldElemOfString "10" F 2]

  solver.assertFormula inv
  solver.assertFormula aIsTwo
  -- -- #TODO requires a cvc5 dyn-lib with *cocoa* linked
  -- assertTrue (← solver.checkSat).isSat
  -- assertEq 2 (← solver.getValue a).getFiniteFieldValue!
  -- assertEq (-2) (← solver.getValue b).getFiniteFieldValue!

  let bIsTwo ← tm.mkTerm Kind.EQUAL #[b, ← tm.mkFiniteFieldElemOfString "2" F]
  solver.assertFormula bIsTwo
  -- -- #TODO requires a cvc5 dyn-lib with *cocoa* linked
  -- assertFalse (← solver.checkSat).isSat
