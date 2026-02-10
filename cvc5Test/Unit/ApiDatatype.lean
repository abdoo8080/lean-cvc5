/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Adrien Champion
-/

import cvc5Test.Init

/-! # Black box testing of the `Command` type

- <https://github.com/cvc5/cvc5/blob/main/test/unit/api/cpp/api_datatype_black.cpp>
-/

namespace cvc5.Test

test![TestApiBlackDatatype, mkDatatypeSort] tm => do
  let int ← tm.getIntegerSort
  let mut dtSpec ← tm.mkDatatypeDecl "list"
  let mut consSpec ← tm.mkDatatypeConstructorDecl "cons"
  consSpec ← consSpec.addSelector "head" int
  dtSpec ← dtSpec.addConstructor consSpec
  let nilSpec ← tm.mkDatatypeConstructorDecl "nil"
  dtSpec ← dtSpec.addConstructor nilSpec
  let listSort ← tm.mkDatatypeSort dtSpec
  let d ← listSort.getDatatype
  let consLen := d.getNumConstructors
  if h : consLen = 2 then
    let consCtor := d[0]
    let nilConstr := d[1]
    assertOkDiscard consCtor.getTerm
    assertOkDiscard nilConstr.getTerm
  else println! "unexpected number of constructors: {d.getNumConstructors}"

test![TestApiBlackDatatype, isNull] tm => do
  let int ← tm.getIntegerSort
  -- creating empty (null) objects
  let mut dtSpec := DatatypeDecl.null ()
  let mut dtConsSpec := DatatypeConstructorDecl.null ()
  let mut dt := Datatype.null ()
  let mut dtCons := DatatypeConstructor.null ()
  let mut dtSel := DatatypeSelector.null ()

  -- verifying that the objects are considered null
  assertTrue dtSpec.isNull
  assertTrue dtConsSpec.isNull
  assertTrue dt.isNull
  assertTrue dtCons.isNull
  assertTrue dtSel.isNull

  -- changing the objects to non-null
  dtSpec ← tm.mkDatatypeDecl "list"
  dtConsSpec ← tm.mkDatatypeConstructorDecl "cons"
  dtConsSpec ← dtConsSpec.addSelector "head" int
  dtSpec ← dtSpec.addConstructor dtConsSpec
  assertEq dtSpec.getNumConstructors 1
  assertFalse dtSpec.isParametric
  let listSort ← tm.mkDatatypeSort dtSpec
  dt ← listSort.getDatatype
  if h : dt.getNumConstructors = 1 then
    dtCons := dt[0]
    if h' : dtCons.getNumSelectors = 1 then
      dtSel := dtCons[0]
    else println! "unexpected number of selectors: {dtCons.getNumSelectors}"
  else println! "unexpected number of constructors: {dt.getNumConstructors}"

  -- verifying that the new objects are non-null
  assertFalse dtSpec.isNull
  assertFalse dtConsSpec.isNull
  assertFalse dt.isNull
  assertFalse dtCons.isNull
  assertFalse dtSel.isNull

  -- testing string representations
  dtCons.toString |> assertEq "cons(head: Int)"
  dtSel.toString |> assertEq "head: Int"
  dtConsSpec.toString |> assertEq "cons(head: Int)"
  dtSpec.toString.trimAscii.toString |> assertEq "DATATYPE list = \ncons(head: Int) END;"
  dt.toString.trimAscii.toString |> assertEq "list"

  -- at this point, the original tests checks the constructor iterator over datatypes; the lean API
  -- is quite different, so there's not much to check besides that it works
  let mut i := 0
  for cons in dt do
    assertFalse cons.isNull
    let cons' := dt[i]!
    i := i + 1
    assertEq cons.toString cons'.toString

test![TestApiBlackDatatype, equalHash] tm => do
  let int ← tm.getIntegerSort

  let mut dt1Spec ← tm.mkDatatypeDecl "list"
  let mut cons1Spec ← tm.mkDatatypeConstructorDecl "cons"
  cons1Spec ← cons1Spec.addSelector "head" int
  dt1Spec ← dt1Spec.addConstructor cons1Spec
  let nil1Spec ← tm.mkDatatypeConstructorDecl "nil"
  dt1Spec ← dt1Spec.addConstructor nil1Spec
  let list1Sort ← tm.mkDatatypeSort dt1Spec
  let list1 ← list1Sort.getDatatype
  let cons1Ctor := list1[0]!
  let nil1Ctor := list1[1]!
  let head1 ← cons1Ctor.getSelector "head"

  let mut dt2Spec ← tm.mkDatatypeDecl "list"
  let mut cons2Spec ← tm.mkDatatypeConstructorDecl "cons"
  cons2Spec ← cons2Spec.addSelector "head" int
  dt2Spec ← dt2Spec.addConstructor cons2Spec
  let nil2Spec ← tm.mkDatatypeConstructorDecl "nil"
  dt2Spec ← dt2Spec.addConstructor nil2Spec
  let list2Sort ← tm.mkDatatypeSort dt2Spec
  let list2 ← list2Sort.getDatatype
  let cons2Ctor := list2[0]!
  let nil2Ctor := list2[1]!
  let head2 ← cons2Ctor.getSelector "head"

  assertEq dt1Spec dt1Spec
  assertNe dt1Spec dt2Spec
  assertEq cons1Spec cons1Spec
  assertNe cons1Spec cons2Spec
  assertEq nil1Spec nil1Spec
  assertNe nil1Spec nil2Spec
  assertEq cons1Ctor cons1Ctor
  assertNe cons1Ctor cons2Ctor
  assertEq nil1Ctor nil1Ctor
  assertNe nil1Ctor nil2Ctor
  assertEq head1 head1
  assertNe head1 head2
  assertEq list1 list1
  assertNe list1 list2

  assertEq dt1Spec.hash dt1Spec.hash
  assertEq dt1Spec.hash dt2Spec.hash
  assertEq cons1Spec.hash cons1Spec.hash
  assertEq cons1Spec.hash cons2Spec.hash
  assertEq nil1Spec.hash nil1Spec.hash
  assertEq nil1Spec.hash nil2Spec.hash
  assertEq cons1Ctor.hash cons1Ctor.hash
  assertEq cons1Ctor.hash cons2Ctor.hash
  assertEq nil1Ctor.hash nil1Ctor.hash
  assertEq nil1Ctor.hash nil2Ctor.hash
  assertEq head1.hash head1.hash
  assertEq head1.hash head2.hash
  assertEq list1.hash list1.hash
  assertEq list1.hash list2.hash

  assertEq 0 (DatatypeDecl.null ()).hash
  assertEq 0 (DatatypeConstructorDecl.null ()).hash
  assertEq 0 (DatatypeConstructor.null ()).hash
  assertEq 0 (DatatypeSelector.null ()).hash
  assertEq 0 (Datatype.null ()).hash

test![TestApiBlackDatatype, mkDatatypeSorts] tm => do
  /-
    Create two mutual datatypes corresponding to these definitions:

    ```
    DATATYPE
      tree = node(left: tree, right: tree) | leaf(data: list),
      list = cons(car: tree, cdr: list) | nil
    END;
    ```
  -/

  -- mark unresolved types as placeholders
  let unresTree ← tm.mkUnresolvedDatatypeSort "tree"
  let unresList ← tm.mkUnresolvedDatatypeSort "list"

  let treeSpec ← do
    let mut treeSpec ← tm.mkDatatypeDecl "tree"
    let mut nodeSpec ← tm.mkDatatypeConstructorDecl "node"
    nodeSpec ← nodeSpec.addSelector "left" unresTree
    nodeSpec ← nodeSpec.addSelector "right" unresTree
    treeSpec ← treeSpec.addConstructor nodeSpec

    let mut leafSpec ← tm.mkDatatypeConstructorDecl "leaf"
    leafSpec ← leafSpec.addSelector "data" unresList
    treeSpec.addConstructor leafSpec

  let listSpec ← do
    let mut listSpec ← tm.mkDatatypeDecl "list"
    let mut consSpec ← tm.mkDatatypeConstructorDecl "cons"
    consSpec ← consSpec.addSelector "car" unresTree
    consSpec ← consSpec.addSelector "cdr" unresTree
    listSpec ← listSpec.addConstructor consSpec
    let mut nilSpec ← tm.mkDatatypeConstructorDecl "nil"
    listSpec.addConstructor nilSpec

  let dtSpecs := #[treeSpec, listSpec]
  let dtSorts ← assertOk <| tm.mkDatatypeSorts dtSpecs
  assertEq dtSpecs.size dtSorts.size

  for h : idx in [:dtSorts.size] do
    let sort := dtSorts[idx]
    assertTrue sort.isDatatype
    assertFalse <| ← assertOk sort.getDatatype!.isFinite
    assertEq sort.getDatatype!.getName! dtSpecs[idx]!.getName!

  -- verify the resolution was correct
  let dtTree := dtSorts[0]!.getDatatype!
  let dtcTreeNode := dtTree[0]!
  assertEq dtcTreeNode.getName! "node"
  let dtsTreeNodeLeft := dtcTreeNode[0]!
  assertEq dtsTreeNodeLeft.getName! "left"
  -- argument type should have resolved to be recursive
  let dtsTreeNodeLeftCodom ← dtsTreeNodeLeft.getCodomainSort
  assertTrue dtsTreeNodeLeftCodom.isDatatype
  assertEq dtsTreeNodeLeftCodom dtSorts[0]!

  -- fails due to empty datatype
  let dtDeclsBad := #[← tm.mkDatatypeDecl "emptyD"]
  tm.mkDatatypeSorts dtDeclsBad |> assertError "\
    invalid datatype declaration in 'dtypedecls' at index 0, \
    expected a datatype declaration with at least one constructor\
  "

test![TestApiBlackDatatype, mkDatatypeSortsSelUnres] tm => do
  -- same as above, without unresolved sorts

  let treeSpec ← do
    let mut treeSpec ← tm.mkDatatypeDecl "tree"
    let mut nodeSpec ← tm.mkDatatypeConstructorDecl "node"
    nodeSpec ← nodeSpec.addSelectorUnresolved "left" "tree"
    nodeSpec ← nodeSpec.addSelectorUnresolved "right" "tree"
    treeSpec ← treeSpec.addConstructor nodeSpec

    let mut leafSpec ← tm.mkDatatypeConstructorDecl "leaf"
    leafSpec ← leafSpec.addSelectorUnresolved "data" "list"
    treeSpec.addConstructor leafSpec

  let listSpec ← do
    let mut listSpec ← tm.mkDatatypeDecl "list"
    let mut consSpec ← tm.mkDatatypeConstructorDecl "cons"
    consSpec ← consSpec.addSelectorUnresolved "car" "tree"
    consSpec ← consSpec.addSelectorUnresolved "cdr" "tree"
    listSpec ← listSpec.addConstructor consSpec
    let mut nilSpec ← tm.mkDatatypeConstructorDecl "nil"
    listSpec.addConstructor nilSpec

  let dtSpecs := #[treeSpec, listSpec]
  let dtSorts ← assertOk <| tm.mkDatatypeSorts dtSpecs
  assertEq dtSpecs.size dtSorts.size

  for h : idx in [:dtSorts.size] do
    let sort := dtSorts[idx]
    assertTrue sort.isDatatype
    assertFalse <| ← assertOk sort.getDatatype!.isFinite
    assertEq sort.getDatatype!.getName! dtSpecs[idx]!.getName!

  -- verify the resolution was correct
  let dtTree := dtSorts[0]!.getDatatype!
  let dtcTreeNode := dtTree[0]!
  assertEq dtcTreeNode.getName! "node"
  let dtsTreeNodeLeft := dtcTreeNode[0]!
  assertEq dtsTreeNodeLeft.getName! "left"
  -- argument type should have resolved to be recursive
  let dtsTreeNodeLeftCodom ← dtsTreeNodeLeft.getCodomainSort
  assertTrue dtsTreeNodeLeftCodom.isDatatype
  assertEq dtsTreeNodeLeftCodom dtSorts[0]!

test![TestApiBlackDatatype, mkDatatypeSortsSelUnres] tm => do
  let int ← tm.getIntegerSort
  let bool ← tm.getBooleanSort

  -- create datatype sort to test
  let mut dtSpec ← tm.mkDatatypeDecl "list"
  let mut consSpec ← tm.mkDatatypeConstructorDecl "cons"
  consSpec ← consSpec.addSelector "head" int
  consSpec ← consSpec.addSelectorSelf "tail"
  let nullSort := cvc5.Sort.null ()
  consSpec.addSelector "null" nullSort |> assertError "invalid null argument for 'sort'"
  dtSpec ← dtSpec.addConstructor consSpec
  let nilSpec ← tm.mkDatatypeConstructorDecl "nil"
  dtSpec ← dtSpec.addConstructor nilSpec
  let dtSort ← tm.mkDatatypeSort dtSpec
  let dt ← dtSort.getDatatype
  assertFalse dt.isCodatatype
  assertFalse dt.isTuple
  assertFalse dt.isRecord
  assertFalse <| ← assertOk dt.isFinite
  assertTrue dt.isWellFounded
  -- get constructor
  let dcons := dt[0]!
  let _ ← dcons.getTerm
  assertEq 2 dcons.getNumSelectors

  -- create datatype sort to test
  let mut dtSpecEnum ← tm.mkDatatypeDecl "enum"
  let ca ← tm.mkDatatypeConstructorDecl "A"
  dtSpecEnum ← dtSpecEnum.addConstructor ca
  let cb ← tm.mkDatatypeConstructorDecl "B"
  dtSpecEnum ← dtSpecEnum.addConstructor cb
  let cc ← tm.mkDatatypeConstructorDecl "C"
  dtSpecEnum ← dtSpecEnum.addConstructor cc
  let dtSortEnum ← tm.mkDatatypeSort dtSpecEnum
  let dtEnum := dtSortEnum.getDatatype!
  assertFalse dtEnum.isTuple
  assertTrue <| ← assertOk dtEnum.isFinite

  -- create codatatype
  let mut dtSpecStream ← tm.mkDatatypeDecl "stream" (isCoDatatype := true)
  let mut consStreamSpec ← tm.mkDatatypeConstructorDecl "cons"
  consStreamSpec ← consStreamSpec.addSelector "head" int
  consStreamSpec ← consStreamSpec.addSelectorSelf "tail"
  dtSpecStream ← dtSpecStream.addConstructor consStreamSpec
  let dtSortStream ← tm.mkDatatypeSort dtSpecStream
  let dtStream := dtSortStream.getDatatype!
  assertTrue dtStream.isCodatatype
  assertFalse <| ← assertOk dtStream.isFinite
  -- codatatypes may be well-founded
  assertTrue dtStream.isWellFounded

  -- create tuple
  let tupSort ← tm.mkTupleSort #[bool]
  let dtTuple := tupSort.getDatatype!
  assertTrue dtTuple.isTuple
  assertFalse dtTuple.isRecord
  assertTrue <| ← assertOk dtTuple.isFinite
  assertTrue dtTuple.isWellFounded

  -- create record
  let fields := #[ ("b", bool), ("i", int) ]
  let recSort ← tm.mkRecordSort fields
  assertTrue recSort.isDatatype
  let dtRecord := recSort.getDatatype!
  assertFalse dtRecord.isTuple
  assertTrue dtRecord.isRecord
  assertFalse <| ← assertOk dtRecord.isFinite
  assertTrue dtRecord.isWellFounded

test![TestApiBlackDatatype, datatypeNames] tm => do
  let int ← tm.getIntegerSort

  -- create datatype sort to test
  let mut dtSpec ← tm.mkDatatypeDecl "list"
  assertEq "list" dtSpec.getName!
  let mut consSpec ← tm.mkDatatypeConstructorDecl "cons"
  consSpec ← consSpec.addSelector "head" int
  consSpec ← consSpec.addSelectorSelf "tail"
  dtSpec ← dtSpec.addConstructor consSpec
  let nil ← tm.mkDatatypeConstructorDecl "nil"
  dtSpec ← dtSpec.addConstructor nil
  let dtSort ← tm.mkDatatypeSort dtSpec
  let dt := dtSort.getDatatype!
  assertError "expected parametric datatype" dt.getParameters
  assertEq "list" dt.getName!
  dt.getConstructor "nil" |> assertOkDiscard
  dt.getConstructor "cons" |> assertOkDiscard
  dt.getConstructor "head" |> assertError
    "no constructor head for datatype list exists, among { cons nil }"
  dt.getConstructor "" |> assertError
    "no constructor  for datatype list exists, among { cons nil }"

  let dcons := dt[0]!
  assertEq "cons" dcons.getName!
  dcons.getSelector "head" |> assertOkDiscard
  dcons.getSelector "tail" |> assertOkDiscard
  dcons.getSelector "cons" |> assertError
    "no selector cons for constructor cons exists among { head tail }"

  -- get selector
  let dselTail := dcons[1]!
  assertEq "tail" dselTail.getName!
  assertEq dtSort (← dselTail.getCodomainSort)

  -- get selector from datatype
  dt.getSelector "head" |> assertOkDiscard
  dt.getSelector "cons" |> assertError "no selector cons for datatype list exists"

  -- possible to construct null datatype declarations if not using solver
  DatatypeDecl.null () |>.getName |> assertError
    "invalid call to 'std::string cvc5::DatatypeDecl::getName() const', expected non-null object"

test![TestApiBlackDatatype, parametricDatatype] tm => do
  let int ← tm.getIntegerSort
  let real ← tm.getRealSort

  let t1 ← tm.mkParamSort "T1"
  let t2 ← tm.mkParamSort "T2"
  let types := #[t1, t2]
  let mut pairSpec ← tm.mkDatatypeDecl "pair" types

  let mut mkPairSpec ← tm.mkDatatypeConstructorDecl "mk-pair"
  mkPairSpec ← mkPairSpec.addSelector "first" t1
  mkPairSpec ← mkPairSpec.addSelector "second" t2
  pairSpec ← pairSpec.addConstructor mkPairSpec

  let pairSort ← tm.mkDatatypeSort pairSpec

  assertTrue pairSort.getDatatype!.isParametric
  let dParams ← pairSort.getDatatype!.getParameters
  assertTrue (dParams[0]! == t1)
  assertTrue (dParams[1]! == t2)

  let pairIntInt ← pairSort.instantiate #[int, int]
  let pairRealReal ← pairSort.instantiate #[real, real]
  let pairRealInt ← pairSort.instantiate #[real, int]
  let pairIntReal ← pairSort.instantiate #[int, real]

  assertNe pairIntInt pairRealReal
  assertNe pairIntReal pairRealReal
  assertNe pairRealInt pairRealReal
  assertNe pairIntInt pairIntReal
  assertNe pairIntInt pairRealInt
  assertNe pairIntReal pairRealInt

test![TestApiBlackDatatype, isFinite] tm => do
  let bool ← tm.getBooleanSort
  let mut dtDecl ← tm.mkDatatypeDecl "dt" #[]
  let mut ctorDecl ← tm.mkDatatypeConstructorDecl "cons"
  ctorDecl ← ctorDecl.addSelector "sel" bool
  dtDecl ← dtDecl.addConstructor ctorDecl
  let dt ← tm.mkDatatypeSort dtDecl
  assertTrue <| ← assertOk dt.getDatatype!.isFinite

  let p ← tm.mkParamSort "p1"
  let mut pDtDecl ← tm.mkDatatypeDecl "dt" #[p]
  let mut pCtorDecl ← tm.mkDatatypeConstructorDecl "cons"
  pCtorDecl ← pCtorDecl.addSelector "sel" p
  pDtDecl ← pDtDecl.addConstructor pCtorDecl
  let pDt ← tm.mkDatatypeSort pDtDecl
  pDt.getDatatype!.isFinite |> assertError
    "invalid call to 'isFinite()', expected non-parametric datatype"

test![TestApiBlackDatatype, datatypeSimplyRec] tm => do
  /- Create mutual datatypes corresponding to this definition block:

  ```
  DATATYPE
    wList = leaf(data: list),
    list = cons(car: wList, cdr: list) | nil,
    ns = elem(ndata: set(wList)) | elemArray(ndata2: array(list, list))
  END;
  ```
  -/

  -- make unresolved types as placeholders
  let unresWList ← tm.mkUnresolvedDatatypeSort "wList"
  let unresList ← tm.mkUnresolvedDatatypeSort "list"

  let mut wListSpec ← tm.mkDatatypeDecl "wList"
  let mut leafSpec ← tm.mkDatatypeConstructorDecl "leaf"
  leafSpec ← leafSpec.addSelector "data" unresList
  wListSpec ← wListSpec.addConstructor leafSpec

  let mut listSpec ← tm.mkDatatypeDecl "list"
  let mut consSpec ← tm.mkDatatypeConstructorDecl "cons"
  consSpec ← consSpec.addSelector "car" unresWList
  consSpec ← consSpec.addSelector "cdr" unresList
  listSpec ← listSpec.addConstructor consSpec
  let nilSpec ← tm.mkDatatypeConstructorDecl "nil"
  listSpec ← listSpec.addConstructor nilSpec

  let mut nsSpec ← tm.mkDatatypeDecl "ns"
  let mut elemSpec ← tm.mkDatatypeConstructorDecl "elem"
  elemSpec ← elemSpec.addSelector "nData" (← tm.mkSetSort unresWList)
  nsSpec ← nsSpec.addConstructor elemSpec
  let mut elemArraySpec ← tm.mkDatatypeConstructorDecl "elemArray"
  elemArraySpec ← elemArraySpec.addSelector "nData" (← tm.mkArraySort unresList unresList)
  nsSpec ← nsSpec.addConstructor elemArraySpec

  let dtDecls := #[wListSpec, listSpec, nsSpec]
  let dtSorts ← assertOk <| tm.mkDatatypeSorts dtDecls
  assertEq 3 dtSorts.size
  assertTrue dtSorts[0]!.getDatatype!.isWellFounded
  assertTrue dtSorts[1]!.getDatatype!.isWellFounded
  assertTrue dtSorts[2]!.getDatatype!.isWellFounded

  /- Create mutual datatypes corresponding to this definition block:

  ```
  DATATYPE
    ns2 = elem2(nData: array(int, ns2)) | nil2
  END;
  ```
  -/
  let unresNs2 ← tm.mkUnresolvedDatatypeSort "ns2"

  let mut ns2Spec ← tm.mkDatatypeDecl "ns2"
  let mut elem2Spec ← tm.mkDatatypeConstructorDecl "elem2"
  let int ← tm.getIntegerSort
  elem2Spec ← elem2Spec.addSelector "nData" (← tm.mkArraySort int unresNs2)
  ns2Spec ← ns2Spec.addConstructor elem2Spec
  let nil2Spec ← tm.mkDatatypeConstructorDecl "nil2"
  ns2Spec ← ns2Spec.addConstructor nil2Spec

  let dtDecls := #[ns2Spec]
  -- this is not well-founded due to non-simple recursion
  let dtSorts ← tm.mkDatatypeSorts dtDecls
  assertEq 1 dtSorts.size
  let codom ← dtSorts[0]!.getDatatype![0]![0]!.getCodomainSort
  assertTrue codom.isArray
  assertEq codom.getArrayElementSort! dtSorts[0]!
  assertTrue dtSorts[0]!.getDatatype!.isWellFounded

  /- Create mutual datatypes corresponding to this definition block:

  ```
  DATATYPE
    list3 = cons3(car: ns3, cdr: list3) | nil3,
    ns3 = elem3(nData: set(list3))
  END;
  ```
  -/
  let unresNs3 ← tm.mkUnresolvedDatatypeSort "ns3"
  let unresList3 ← tm.mkUnresolvedDatatypeSort "list3"

  let mut list3Spec ← tm.mkDatatypeDecl "list3"
  let mut cons3Spec ← tm.mkDatatypeConstructorDecl "cons3"
  cons3Spec ← cons3Spec.addSelector "car" unresNs3
  cons3Spec ← cons3Spec.addSelector "cdr" unresList3
  list3Spec ← list3Spec.addConstructor cons3Spec
  let nil3Spec ← tm.mkDatatypeConstructorDecl "nil3"
  list3Spec ← list3Spec.addConstructor nil3Spec

  let mut ns3Spec ← tm.mkDatatypeDecl "ns3"
  let mut elem3Spec ← tm.mkDatatypeConstructorDecl "elem3"
  elem3Spec ← elem3Spec.addSelector "nData" (← tm.mkSetSort unresList3)
  ns3Spec ← ns3Spec.addConstructor elem3Spec

  let dtDecls := #[list3Spec, ns3Spec]

  -- both are well-founded and have nested recursion
  let dtSorts ← tm.mkDatatypeSorts dtDecls
  assertEq 2 dtSorts.size
  assertTrue dtSorts[0]!.getDatatype!.isWellFounded
  assertTrue dtSorts[1]!.getDatatype!.isWellFounded

  /- Create mutual datatypes corresponding to this definition block:

  ```
  DATATYPE
    list4 = cons(car: set(ns4), cdr: list4) | nil,
    ns4 = elem(nData: list4)
  END;
  ```
  -/
  let unresNs4 ← tm.mkUnresolvedDatatypeSort "ns4"
  let unresList4 ← tm.mkUnresolvedDatatypeSort "list4"

  let mut list4Spec ← tm.mkDatatypeDecl "list4"
  let mut cons4Spec ← tm.mkDatatypeConstructorDecl "cons4"
  cons4Spec ← cons4Spec.addSelector "car" (← tm.mkSetSort unresNs4)
  cons4Spec ← cons4Spec.addSelector "cdr" unresList4
  list4Spec ← list4Spec.addConstructor cons4Spec
  let nil4Spec ← tm.mkDatatypeConstructorDecl "nil4"
  list4Spec ← list4Spec.addConstructor nil4Spec

  let mut ns4Spec ← tm.mkDatatypeDecl "ns4"
  let mut elem4Spec ← tm.mkDatatypeConstructorDecl "elem4"
  elem4Spec ← elem4Spec.addSelector "nData" unresList4
  ns4Spec ← ns4Spec.addConstructor elem4Spec

  let dtDecls := #[list4Spec, ns4Spec]
  let dtSorts ← tm.mkDatatypeSorts dtDecls
  assertEq 2 dtSorts.size
  assertTrue dtSorts[0]!.getDatatype!.isWellFounded
  assertTrue dtSorts[1]!.getDatatype!.isWellFounded

  /- Create mutual datatypes corresponding to this definition block:

  ```
  DATATYPE
    list5[X] = cons(car: X, cdr: list5[list5[X]]) | nil
  END;
  ```
  -/
  let unresList5 ← tm.mkUninterpretedSortConstructorSort 1 "list5"

  let xSort ← tm.mkParamSort "X"

  let mut list5Spec ← tm.mkDatatypeDecl "list5 sortParams" #[xSort]
  let urListX ← unresList5.instantiate #[xSort]
  let urListListX ← unresList5.instantiate #[urListX]

  let mut cons5Spec ← tm.mkDatatypeConstructorDecl "cons5"
  cons5Spec ← cons5Spec.addSelector "car" xSort
  cons5Spec ← cons5Spec.addSelector "cdr" urListListX
  list5Spec ← list5Spec.addConstructor cons5Spec
  let nil5Spec ← tm.mkDatatypeConstructorDecl "nil5"
  list5Spec ← list5Spec.addConstructor nil5Spec

  -- well-founded and has nested recursion
  let dtSorts ← tm.mkDatatypeSorts #[list5Spec]
  assertEq 1 dtSorts.size
  assertTrue dtSorts[0]!.getDatatype!.isWellFounded

test![TestApiBlackDatatype, datatypeSpecializedCons] tm => do
  /- Create mutual datatypes corresponding to this definition block:

  ```
  DATATYPE
    pList[X] = pCons(car: X, cdr: pList[X]) | pNil
  END;
  ```
  -/
  -- make unresolved types as placeholders
  let unresList ← tm.mkUninterpretedSortConstructorSort 1 "pList"

  let xSort ← tm.mkParamSort "X"
  let mut pListSpec ← tm.mkDatatypeDecl "pList" #[xSort]

  let urListX ← unresList.instantiate #[xSort]
  let mut pConsSpec ← tm.mkDatatypeConstructorDecl "pCons"
  pConsSpec ← pConsSpec.addSelector "car" xSort
  pConsSpec ← pConsSpec.addSelector "cdr" urListX
  pListSpec ← pListSpec.addConstructor pConsSpec
  let nil5Spec ← tm.mkDatatypeConstructorDecl "pNil"
  pListSpec ← pListSpec.addConstructor nil5Spec

  let dtSorts ← tm.mkDatatypeSorts #[pListSpec]
  assertEq 1 dtSorts.size
  let dt ← dtSorts[0]!.getDatatype
  let nilCtor := dt[0]!

  let int ← tm.getIntegerSort
  let listInt ← dtSorts[0]!.instantiate #[int]

  let liParams ← listInt.getDatatype!.getParameters
  -- the parameter of the datatype is not instantiated
  assertEq 1 liParams.size
  assertEq xSort liParams[0]!

  let testConsTerm ← nilCtor.getInstantiatedTerm listInt
  assertNe testConsTerm (← nilCtor.getTerm)
  -- error to get the specialized constructor term for `Int`
  nilCtor.getInstantiatedTerm int |> assertError
    "cannot get specialized constructor type for non-datatype type Int"
