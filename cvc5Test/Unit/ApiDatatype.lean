/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Adrien Champion
-/

import cvc5Test.Init

/-! # Black box testing of the `Command` type

- <https://github.com/cvc5/cvc5/blob/main/test/unit/api/cpp/api_command_black.cpp>
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
    let _consConstrTerm := consConstr.getTerm
    let _nilConstrTerm := nilConstr.getTerm
  else
    println! "unexpected number of constructors: {d.getNumConstructors}"
