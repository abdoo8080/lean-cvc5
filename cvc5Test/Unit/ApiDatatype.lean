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
  let mut cons ← tm.mkDatatypeConstructorDecl "cons"
  cons ← cons.addSelector "head" int
  dtSpec ← dtSpec.addConstructor cons
  let nil ← tm.mkDatatypeConstructorDecl "nil"
  dtSpec ← dtSpec.addConstructor nil
  let listSort ← tm.mkDatatypeSort dtSpec
  let d ← listSort.getDatatype
  let consLen := d.getNumConstructors
  if h : consLen = 2 then
    let consConstr := d[0]
    let nilConstr := d[1]
    assertOkDiscard consConstr.getTerm
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
  dtSpec.toString.trim |> assertEq "DATATYPE list = \ncons(head: Int) END;"
  dt.toString.trim |> assertEq "list"

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

  let mut dtSpec1 ← tm.mkDatatypeDecl "list"
  let mut cons1 ← tm.mkDatatypeConstructorDecl "cons"
  cons1 ← cons1.addSelector "head" int
  dtSpec1 ← dtSpec1.addConstructor cons1
  let nil1 ← tm.mkDatatypeConstructorDecl "nil"
  dtSpec1 ← dtSpec1.addConstructor nil1
  let listSort1 ← tm.mkDatatypeSort dtSpec1
  let list1 ← listSort1.getDatatype
  let consConstr1 := list1[0]!
  let nilConstr1 := list1[1]!
  let head1 ← consConstr1.getSelector "head"

  let mut dtSpec2 ← tm.mkDatatypeDecl "list"
  let mut cons2 ← tm.mkDatatypeConstructorDecl "cons"
  cons2 ← cons2.addSelector "head" int
  dtSpec2 ← dtSpec2.addConstructor cons2
  let nil2 ← tm.mkDatatypeConstructorDecl "nil"
  dtSpec2 ← dtSpec2.addConstructor nil2
  let listSort2 ← tm.mkDatatypeSort dtSpec2
  let list2 ← listSort2.getDatatype
  let consConstr2 := list2[0]!
  let nilConstr2 := list2[1]!
  let head2 ← consConstr2.getSelector "head"

  assertEq dtSpec1 dtSpec1
  assertNe dtSpec1 dtSpec2
  assertEq cons1 cons1
  assertNe cons1 cons2
  assertEq nil1 nil1
  assertNe nil1 nil2
  assertEq consConstr1 consConstr1
  assertNe consConstr1 consConstr2
  assertEq nilConstr1 nilConstr1
  assertNe nilConstr1 nilConstr2
  assertEq head1 head1
  assertNe head1 head2
  assertEq list1 list1
  assertNe list1 list2

  assertEq dtSpec1.hash dtSpec1.hash
  assertEq dtSpec1.hash dtSpec2.hash
  assertEq cons1.hash cons1.hash
  assertEq cons1.hash cons2.hash
  assertEq nil1.hash nil1.hash
  assertEq nil1.hash nil2.hash
  assertEq consConstr1.hash consConstr1.hash
  assertEq consConstr1.hash consConstr2.hash
  assertEq nilConstr1.hash nilConstr1.hash
  assertEq nilConstr1.hash nilConstr2.hash
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
    assertFalse sort.getDatatype!.isFinite
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
    assertFalse sort.getDatatype!.isFinite
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
  assertFalse dt.isFinite
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
  assertTrue dtEnum.isFinite

  -- create codatatype
  let mut dtSpecStream ← tm.mkDatatypeDecl "stream" (isCoDatatype := true)
  let mut consStreamSpec ← tm.mkDatatypeConstructorDecl "cons"
  consStreamSpec ← consStreamSpec.addSelector "head" int
  consStreamSpec ← consStreamSpec.addSelectorSelf "tail"
  dtSpecStream ← dtSpecStream.addConstructor consStreamSpec
  let dtSortStream ← tm.mkDatatypeSort dtSpecStream
  let dtStream := dtSortStream.getDatatype!
  assertTrue dtStream.isCodatatype
  assertFalse dtStream.isFinite
  -- codatatypes may be well-founded
  assertTrue dtStream.isWellFounded

  -- create tuple
  let tupSort ← tm.mkTupleSort #[bool]
  let dtTuple := tupSort.getDatatype!
  assertTrue dtTuple.isTuple
  assertFalse dtTuple.isRecord
  assertTrue dtTuple.isFinite
  assertTrue dtTuple.isWellFounded

  -- create record
  let fields := #[ ("b", bool), ("i", int) ]
  let recSort ← tm.mkRecordSort fields
  assertTrue recSort.isDatatype
  let dtRecord := recSort.getDatatype!
  assertFalse dtRecord.isTuple
  assertTrue dtRecord.isRecord
  assertFalse dtRecord.isFinite
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
