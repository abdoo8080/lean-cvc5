/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Adrien Champion
-/

import cvc5Test.Init

/-! # Black box testing of the `Grammar` type

- <https://github.com/cvc5/cvc5/blob/main/test/unit/api/cpp/api_grammar_black.cpp>
-/

namespace cvc5.Test

def sygusSolver (tm : TermManager) : Env Solver := do
  let solver ← Solver.new tm
  solver.setOption "sygus" "true"
  return solver

test![TestApiBlackGrammar, toString] tm => do
  let solver ← sygusSolver tm
  let bool ← tm.getBooleanSort
  let start ← tm.mkVar bool "start"
  let mut grammar ← solver.mkGrammar #[] #[start]
  assertEq grammar.toString ""
  grammar ← grammar.addRule start (← tm.mkBoolean false)
  assertEq grammar.toString "((start Bool) )((start Bool (false)))"

test![TestApiBlackGrammar, addRule] tm => do
  let solver ← sygusSolver tm
  let bool ← tm.getBooleanSort
  let nullTerm := Term.null ()
  let start ← tm.mkVar bool "start"
  let nts ← tm.mkVar bool "nts"
  let mut grammar ← solver.mkGrammar #[] #[start]
  let fls ← tm.mkBoolean false

  grammar ← grammar.addRule start fls |> assertOk

  grammar.addRule nullTerm fls |> assertError
    "invalid null argument for 'ntSymbol'"
  grammar.addRule start nullTerm |> assertError
    "invalid null argument for 'rule'"
  grammar.addRule nts fls |> assertError
    "invalid argument 'nts' for 'ntSymbol', \
    expected ntSymbol to be one of the non-terminal symbols given in the predeclaration"
  grammar.addRule start (← tm.mkInteger 0) |> assertError
    "expected ntSymbol and rule to have the same sort"

  solver.synthFun "f" #[] bool grammar |> assertOkDiscard

  grammar.addRule start fls |> assertError
    "Grammar cannot be modified after passing it as an argument to synthFun"

test![TestApiBlackGrammar, addRules] tm => do
  let solver ← sygusSolver tm
  let bool ← tm.getBooleanSort
  let nullTerm := Term.null ()
  let start ← tm.mkVar bool "start"
  let nts ← tm.mkVar bool "nts"
  let mut grammar ← solver.mkGrammar #[] #[start]
  let fls ← tm.mkBoolean false

  grammar ← grammar.addRules start #[fls] |> assertOk

  grammar.addRules nullTerm #[fls] |> assertError
    "invalid null argument for 'ntSymbol'"
  grammar.addRules start #[nullTerm] |> assertError
    "invalid null term in 'rules' at index 0"
  grammar.addRules nts #[fls] |> assertError
    "invalid argument 'nts' for 'ntSymbol', \
    expected ntSymbol to be one of the non-terminal symbols given in the predeclaration"
  grammar.addRules start #[← tm.mkInteger 0] |> assertError
    "Expected term with sort Bool at index 0 in rules"

  solver.synthFun "f" #[] bool grammar |> assertOkDiscard

  grammar.addRules start #[fls] |> assertError
    "Grammar cannot be modified after passing it as an argument to synthFun"

test![TestApiBlackGrammar, addAnyConstant] tm => do
  let solver ← sygusSolver tm
  let bool ← tm.getBooleanSort
  let nullTerm := Term.null ()
  let start ← tm.mkVar bool "start"
  let nts ← tm.mkVar bool "nts"
  let mut grammar ← solver.mkGrammar #[] #[start]

  grammar ← grammar.addAnyConstant start |> assertOk
  grammar ← grammar.addAnyConstant start |> assertOk

  grammar.addAnyConstant nullTerm |> assertError
    "invalid null argument for 'ntSymbol'"
  grammar.addAnyConstant nts |> assertError
    "invalid argument 'nts' for 'ntSymbol', \
    expected ntSymbol to be one of the non-terminal symbols given in the predeclaration"

  solver.synthFun "f" #[] bool grammar |> assertOkDiscard

  grammar.addAnyConstant start |> assertError
    "Grammar cannot be modified after passing it as an argument to synthFun"

test![TestApiBlackGrammar, addAnyVariable] tm => do
  let solver ← sygusSolver tm
  let bool ← tm.getBooleanSort
  let nullTerm := Term.null ()
  let x ← tm.mkVar bool "x"
  let start ← tm.mkVar bool "start"
  let nts ← tm.mkVar bool "nts"

  let mut grammar1 ← solver.mkGrammar #[ x ] #[start]
  let mut grammar2 ← solver.mkGrammar #[] #[start]

  grammar1 ← grammar1.addAnyVariable start |> assertOk
  grammar1 ← grammar1.addAnyVariable start |> assertOk
  grammar2 ← grammar2.addAnyVariable start |> assertOk
  -- silence warning that `grammar2` is unused
  let _ := grammar2

  grammar1.addAnyVariable nullTerm |> assertError
    "invalid null argument for 'ntSymbol'"
  grammar1.addAnyVariable nts |> assertError
    "invalid argument 'nts' for 'ntSymbol', \
    expected ntSymbol to be one of the non-terminal symbols given in the predeclaration"

  solver.synthFun "f" #[] bool grammar1 |> assertOkDiscard

  grammar1.addAnyVariable start |> assertError
    "Grammar cannot be modified after passing it as an argument to synthFun"

test![TestApiBlackGrammar, equalHash] tm => do
  let solver ← sygusSolver tm
  let bool ← tm.getBooleanSort
  let x ← tm.mkVar bool "x"
  let start1 ← tm.mkVar bool "start"
  let start2 ← tm.mkVar bool "start"
  let fls ← tm.mkBoolean false

  let run : Env Unit → Env Unit := id

  run do
    let g1 ← solver.mkGrammar #[] #[start1]
    let g2 ← solver.mkGrammar #[] #[start1]
    assertEq g1.hash g1.hash
    assertEq g1.hash g2.hash
    assertTrue (g1 == g1)
    assertFalse (g1 == g2)

  run do
    let g1 ← solver.mkGrammar #[] #[start1]
    let g2 ← solver.mkGrammar #[ x ] #[start2]
    assertNe g1.hash g2.hash
    assertTrue (g1 == g1)
    assertFalse (g1 == g2)

  run do
    let g1 ← solver.mkGrammar #[ x ] #[start1]
    let g2 ← solver.mkGrammar #[ x ] #[start2]
    assertNe g1.hash g2.hash
    assertTrue (g1 == g1)
    assertFalse (g1 == g2)

  run do
    let g1 ← solver.mkGrammar #[ x ] #[start1]
    let mut g2 ← solver.mkGrammar #[ x ] #[start1]
    g2 ← g2.addAnyVariable start1
    assertNe g1.hash g2.hash
    assertTrue (g1 == g1)
    assertFalse (g1 == g2)

  run do
    let mut g1 ← solver.mkGrammar #[ x ] #[start1]
    let mut g2 ← solver.mkGrammar #[ x ] #[start1]
    let rules := #[fls]
    g1 ← g1.addRules start1 rules
    g2 ← g2.addRules start1 rules
    assertEq g1.hash g2.hash
    assertTrue (g1 == g1)
    assertFalse (g1 == g2)

  run do
    let g1 ← solver.mkGrammar #[ x ] #[start1]
    let mut g2 ← solver.mkGrammar #[ x ] #[start1]
    let rules2 := #[fls]
    g2 ← g2.addRules start1 rules2
    assertNe g1.hash g2.hash
    assertTrue (g1 == g1)
    assertFalse (g1 == g2)

  run do
    let mut g1 ← solver.mkGrammar #[ x ] #[start1]
    let mut g2 ← solver.mkGrammar #[ x ] #[start1]
    let rules1 := #[← tm.mkBoolean true]
    let rules2 := #[fls]
    g1 ← g1.addRules start1 rules1
    g2 ← g2.addRules start1 rules2
    assertNe g1.hash g2.hash
    assertTrue (g1 == g1)
    assertFalse (g1 == g2)
