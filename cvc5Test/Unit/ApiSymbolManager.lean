import cvc5Test.Init

/-! # Black box testing of the `SymbolManager` type

- <https://github.com/cvc5/cvc5/blob/main/test/unit/api/cpp/api_symbol_manager_black.cpp>
-/

namespace cvc5.Test

def parseCommand (solver : Solver) (parser : InputParser) (cmd : String)
  (checkOutput : String → Env Unit := (assertEq · ""))
: Env Unit := do
  parser.setStringInput cmd
  let cmd ← parser.nextCommand
  let output ← cmd.invoke solver (← parser.getSymbolManager)
  checkOutput output

def parseLogic (solver : Solver) (parser : InputParser) (logic : String) : Env Unit :=
  parseCommand solver parser s!"(set-logic {logic})"

test![TestApiBlackSymbolManager, isLogicSet] tm => do
  let solver ← Solver.new tm
  let parser ← InputParser.new solver
  let sm ← parser.getSymbolManager
  assertFalse (← sm.isLogicSet)
  parseLogic solver parser "QF_LIA"
  assertTrue (← sm.isLogicSet)

test![TestApiBlackSymbolManager, getLogic] tm => do
  let solver ← Solver.new tm
  let parser ← InputParser.new solver
  let sm ← parser.getSymbolManager
  assertError "invalid call to 'getLogic', logic has not yet been set"
    sm.getLogic
  parseLogic solver parser "QF_LIA"
  assertEq (← sm.getLogic) "QF_LIA"

test![TestApiBlackSymbolManager, getDeclaredTermsAndSorts] tm => do
  let solver ← Solver.new tm
  let parser ← InputParser.new solver
  let sm ← parser.getSymbolManager
  assertEq (← sm.getDeclaredSorts) #[]
  assertEq (← sm.getDeclaredTerms) #[]
