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

def parseCommand (parser : InputParser) (s : String) : Env Command := do
  parser.appendIncrementalStringInput s
  parser.nextCommand

test![TestApiBlackCommand, invoke] tm => do
  let solver ← Solver.new tm
  let parser ← InputParser.new solver
  let sm ← parser.getSymbolManager
  parser.setIncrementalStringInput
  let mut cmd ← parseCommand parser "(set-logic QF_LIA)"
  assertFalse cmd.isNull
  let _ ← cmd.invoke solver sm
  cmd ← parseCommand parser "(get-model)"
  assertFalse cmd.isNull
  let output ← String.trim <$> cmd.invoke solver sm
  assertEq output
    "(error \"cannot get model unless model generation is enabled (try --produce-models)\")"
  assertError "Only one set-logic is allowed." do
    parseCommand parser "(set-logic QF_LRA)"

test![TestApiBlackCommand, toString] tm => do
  let solver ← Solver.new tm
  let parser ← InputParser.new solver
  parser.setIncrementalStringInput
  let cmd ← parseCommand parser "(set-logic QF_LIA)"
  assertFalse cmd.isNull
  assertEq cmd.toString "(set-logic QF_LIA)"

test![TestApiBlackCommand, getCommandName] tm => do
  let solver ← Solver.new tm
  let parser ← InputParser.new solver
  parser.setIncrementalStringInput
  let cmd ← parseCommand parser "(get-model)"
  assertFalse cmd.isNull
  assertEq cmd.getCommandName "get-model"
