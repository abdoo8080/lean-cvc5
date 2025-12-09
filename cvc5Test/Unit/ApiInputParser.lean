/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Adrien Champion
-/

import cvc5Test.Init

/-! # Black box testing of the `InputParser` type

- <https://github.com/cvc5/cvc5/blob/main/test/unit/api/cpp/api_input_parser_black.cpp>
-/

namespace cvc5.Test

def parseLogicCommand (parser : InputParser) (logic : String) : Env Command := do
  parser.setIncrementalStringInput (name := "parserUnitTests")
  parser.appendIncrementalStringInput s!"(set-logic {logic})"
  parser.nextCommand

test![TestApiBlackInputParser, constructSymbolManager] tm => do
  let _ ← SymbolManager.new tm

test![TestApiBlackInputParser, setFileInput] tm => do
  let solver ← Solver.new tm
  let parser ← InputParser.new solver
  assertError "Couldn't open file: nonexistent.smt2" do
    parser.setFileInput "nonexistent.smt2"

test![TestApiBlackInputParser, setStreamInput] tm => do
  let solver ← Solver.new tm
  let parser ← InputParser.new solver
  let symbols ← parser.getSymbolManager
  let s := "(set-logic QF_LIA)\n(declare-fun a () Bool)\n(declare-fun b () Bool)\n"
  parser.setStringInput s (name := "input_parser_black")
  assertFalse (← parser.isDone)
  let rec loop (_ : Unit) : Env Unit := do
    let cmd ← parser.nextCommand
    if cmd.isNull then return ()
    cmd.invoke solver symbols |> assertOkDiscard
    loop ()
  loop ()
  assertTrue (← parser.isDone)

test![TestApiBlackInputParser, setStreamInput'] tm => do
  let solver ← Solver.new tm
  let parser ← InputParser.new solver
  let symbols ← parser.getSymbolManager
  let s := "(set-logic QF_LIA)\n(declare-fun a () Bool)\n(declare-fun b () Bool)\n"
  parser.setStringInput s (name := "input_parser_black")
  assertFalse (← parser.isDone)
  let rec loop (_ : Unit) : Env Unit := do
    match ← parser.nextCommand? with
    | some cmd =>
      cmd.invoke solver symbols |> assertOkDiscard
      loop ()
    | none => return ()
  loop ()
  assertTrue (← parser.isDone)

test![TestApiBlackInputParser, setAndAppendIncrementalStringInput] tm => do
  let solver ← Solver.new tm
  let parser ← InputParser.new solver
  let symbols ← parser.getSymbolManager
  parser.setIncrementalStringInput (name := "input_parser_black")
  assertFalse (← parser.isDone)
  parser.appendIncrementalStringInput "(set-logic QF_LIA)"
  parser.appendIncrementalStringInput "(declare-fun a () Bool)"
  parser.appendIncrementalStringInput "(declare-fun b () Int)"
  let cmd ← parser.nextCommand
  assertFalse cmd.isNull
  cmd.invoke solver symbols |> assertOkDiscard
  let cmd ← parser.nextCommand
  assertFalse cmd.isNull
  cmd.invoke solver symbols |> assertOkDiscard
  let cmd ← parser.nextCommand
  assertFalse cmd.isNull
  cmd.invoke solver symbols |> assertOkDiscard
  assertFalse (← parser.isDone)
  let cmd ← parser.nextCommand
  assertTrue cmd.isNull
  assertTrue (← parser.isDone)

test![TestApiBlackInputParser, setAndAppendIncrementalStringInputInterleave] tm => do
  let solver ← Solver.new tm
  let parser ← InputParser.new solver
  let symbols ← parser.getSymbolManager
  parser.setIncrementalStringInput (name := "input_parser_black")
  assertFalse (← parser.isDone)
  parser.appendIncrementalStringInput "(set-logic QF_LIA)"
  let cmd ← parser.nextCommand
  assertFalse cmd.isNull
  cmd.invoke solver symbols |> assertOkDiscard
  parser.appendIncrementalStringInput "(declare-fun a () Bool)"
  let cmd ← parser.nextCommand
  assertFalse cmd.isNull
  cmd.invoke solver symbols |> assertOkDiscard
  parser.appendIncrementalStringInput "(declare-fun b () Int)"
  let cmd ← parser.nextCommand
  assertFalse cmd.isNull
  cmd.invoke solver symbols |> assertOkDiscard
  assertFalse (← parser.isDone)
  let cmd ← parser.nextCommand
  assertTrue cmd.isNull
  assertTrue (← parser.isDone)

test![TestApiBlackInputParser, appendIncrementalNoSet] tm => do
  let solver ← Solver.new tm
  let parser ← InputParser.new solver
  assertError "Input to parser not initialized" do
    parser.appendIncrementalStringInput "(set-logic ALL)"

test![TestApiBlackInputParser, setStringInput] tm => do
  let solver ← Solver.new tm
  let parser ← InputParser.new solver
  let symbols ← parser.getSymbolManager
  parser.setStringInput "(set-logic ALL)" (name := "input_parser_black")
  let cmd ← parser.nextCommand
  assertFalse cmd.isNull
  cmd.invoke solver symbols |> assertOkDiscard
  let cmd ← parser.nextCommand
  assertTrue cmd.isNull

test![TestApiBlackInputParser, nextCommandNoInput] tm => do
  let solver ← Solver.new tm
  let parser ← InputParser.new solver
  parser.setStringInput "" (name := "input_parser_black")
  let cmd ← parser.nextCommand
  assertTrue cmd.isNull

test![TestApiBlackInputParser, nextCommandNoIncrementalInput] tm => do
  let solver ← Solver.new tm
  let parser ← InputParser.new solver
  parser.setIncrementalStringInput (name := "input_parser_black")
  let cmd ← parser.nextCommand
  assertTrue cmd.isNull
  let term ← parser.nextTerm
  assertTrue term.isNull

test![TestApiBlackInputParser, nextTerm] tm => do
  let solver ← Solver.new tm
  let parser ← InputParser.new solver
  assertError "Input to parser not initialized" parser.nextTerm
  parser.setStringInput "" (name := "input_parser_black")
  let term ← parser.nextTerm
  assertTrue term.isNull

test![TestApiBlackInputParser, nextTerm2] tm => do
  let solver ← Solver.new tm
  -- adding a set-logic compared to the original test to silence warnings
  solver.setLogic "ALL"
  let parser ← InputParser.new solver
  let symbols ← parser.getSymbolManager
  assertError "Input to parser not initialized" parser.nextTerm
  parser.setIncrementalStringInput (name := "input_parser_black")
  -- parse a declaration command
  parser.appendIncrementalStringInput "(declare-fun a () Int)\n"
  let cmd ← parser.nextCommand
  assertFalse cmd.isNull
  cmd.invoke solver symbols |> assertOkDiscard
  -- now parse some terms
  parser.appendIncrementalStringInput "45\n"
  let term ← assertOk parser.nextTerm
  assertFalse term.isNull
  parser.appendIncrementalStringInput "(+ a 1)\n"
  let term ← assertOk parser.nextTerm
  assertFalse term.isNull
  assertEq term.getKind Kind.ADD
  parser.appendIncrementalStringInput "(+ b 1)\n"
  assertError "Symbol 'b' not declared as a variable" parser.nextTerm

test![TestApiBlackInputParser, setAndAppendIncrementalStringInput] tm => do
  let solver1 ← Solver.new tm
  let parser1 ← InputParser.new solver1
  let symbols ← parser1.getSymbolManager
  -- set a logic for the parser
  let cmd ← parseLogicCommand parser1 "QF_LIA"
  cmd.invoke solver1 symbols |> assertOkDiscard
  assertTrue (← solver1.isLogicSet)
  assertEq (← solver1.getLogic) "QF_LIA"
  assertEq (← solver1.getLogic?) "QF_LIA"
  assertTrue (← symbols.isLogicSet)
  assertEq (← symbols.getLogic) "QF_LIA"
  -- cannot set logic on solver now
  solver1.setLogic "QF_LRA" |> assertError
    "invalid call to 'setLogic', logic is already set"

  -- possible to construct another parser with the same solver and symbol manager
  let _parser1' ← InputParser.new solver1 symbols

  -- possible to construct another parser with a fresh solver
  let solver2 ← Solver.new tm
  let parser2 ← InputParser.new solver2 symbols
  parser2.setIncrementalStringInput (name := "input_parser_black")
  -- logic is automatically set on the solver
  assertTrue (← solver2.isLogicSet)
  assertEq (← solver2.getLogic) "QF_LIA"
  assertEq (← solver2.getLogic?) "QF_LIA"
  -- we cannot set the logic since it has already been set
  parseLogicCommand parser2 "QF_LRA" |> assertError
    "Only one set-logic is allowed."

  -- using a solver with the same logic is allowed
  let solver3 ← Solver.new tm
  solver3.setLogic "QF_LIA"
  let parser3 ← InputParser.new solver3 symbols
  parser3.setIncrementalStringInput (name := "input_parser_black")

  -- using a solver with a different logic is not allowed
  let solver4 ← Solver.new tm
  solver4.setLogic "QF_LRA"
  let parser4 ← InputParser.new solver4 symbols
  parser4.setIncrementalStringInput (name := "input_parser_black") |> assertError
    "Logic mismatch when initializing InputParser.\n\
    The solver's logic: QF_LRA\nThe symbol manager's logic: QF_LIA"

test![TestApiBlackInputParser, incrementalSetString] tm => do
  let solver ← Solver.new tm
  let parser ← InputParser.new solver
  let symbols ← parser.getSymbolManager
  let mut out := ""
  let commands :=
    ["(set-logic ALL)", "(push)", "(declare-fun x () Int)", "(pop)", "(declare-fun x () Int)"]
  for command in commands do
    parser.setStringInput command
    let cmd ← parser.nextCommand
    assertFalse cmd.isNull
    let output ← cmd.invoke solver symbols |> assertOk
    out := s!"{out}{output}"
  assertEq out ""

test![TestApiBlackInputParser, getDeclaredTermsAndSorts] tm => do
  let solver ← Solver.new tm
  let parser ← InputParser.new solver
  let symbols ← parser.getSymbolManager
  parser.setIncrementalStringInput (name := "input_parser_black")
  parser.appendIncrementalStringInput "(set-logic ALL)"
  parser.appendIncrementalStringInput "(declare-sort U 0)"
  parser.appendIncrementalStringInput "(declare-fun x () U)"
  for _ in [1, 2, 3] do
    let cmd ← parser.nextCommand
    assertFalse cmd.isNull
    cmd.invoke solver symbols |> assertOkDiscard
  let sorts ← symbols.getDeclaredSorts
  let terms ← symbols.getDeclaredTerms
  assertEq sorts.size 1
  assertEq terms.size 1
  assertEq terms[0]!.getSort sorts[0]!
