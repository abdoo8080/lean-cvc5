/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Adrien Champion
-/

import cvc5Test.Init

/-! # Black box testing of the `SynthResult` type

- <https://github.com/cvc5/cvc5/blob/main/test/unit/api/cpp/api_synth_result_black.cpp>
-/

namespace cvc5.Test

test![TestApiBlackSynthResult, isNull] do
  -- null `SynthResult` cannot be constructed, skipping test
  return ()

test![TestApiBlackSynthResult, hasSolution] tm => do
  let solver ← Solver.new tm
  solver.setOption "sygus" "true"
  let bool ← tm.getBooleanSort
  let _f ← solver.synthFun "f" #[] bool
  let tru ← tm.mkBoolean true
  solver.addSygusConstraint tru
  let res ← solver.checkSynth
  assertFalse res.isNull
  assertTrue res.hasSolution
  assertFalse res.hasNoSolution
  assertFalse res.isUnknown
  assertEq res.toString "(SOLUTION)"

test![TestApiBlackSynthResult, hasNoSolution] tm => do
  let solver ← Solver.new tm
  solver.setOption "sygus" "true"
  let bool ← tm.getBooleanSort
  let _f ← solver.synthFun "f" #[] bool
  let fls ← tm.mkBoolean false
  solver.addSygusConstraint fls
  let res ← solver.checkSynth
  assertFalse res.isNull
  assertFalse res.hasSolution
  assertTrue res.hasNoSolution
  assertFalse res.isUnknown
  assertEq res.toString "(NO_SOLUTION)"

test![TestApiBlackSynthResult, isUnknown] do
  -- no test for `SynthResult.isUnknown`
  return ()

test![TestApiBlackSynthResult, equalHash] tm => do
  let solver ← Solver.new tm
  solver.setOption "sygus" "true"
  let bool ← tm.getBooleanSort
  let _f ← solver.synthFun "f" #[] bool
  let tru ← tm.mkBoolean true
  solver.addSygusConstraint tru
  let res1 ← solver.checkSynth
  let fls ← tm.mkBoolean false
  solver.addSygusConstraint fls
  let res2 ← solver.checkSynth
  assertEq res1 res1
  assertNe res1 res2
  assertEq res1.hash res1.hash
  assertNe res1.hash res2.hash
