/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Lean.Elab.Parallel

/-!
# Tests for Iterator-based parallel execution

Tests for `Lean.Elab.Parallel`, verifying:
- Tasks complete in parallel and results are returned in completion order
- State is properly threaded through CoreM/MetaM/TacticM iterations
- Cancellation hooks work with cooperative cancellation via `CancelToken`
-/

open Std.Iterators

/-- Create a test environment with the given imports. -/
def mkCoreState (imports : Array Lean.Import) (loadExts : Bool := false) :
    IO (Lean.Core.Context × Lean.Core.State) := do
  let env ← Lean.importModules imports {} 0 (loadExts := loadExts)
  return (
    { fileName := "<test>", fileMap := default },
    { env := env }
  )

/-- Run a TacticM test with a fresh True goal. -/
def runTacticTest {α : Type} (test : Lean.Elab.Tactic.TacticM α) : IO α := do
  let (coreCtx, coreState) ← mkCoreState #[{module := `Init}] (loadExts := true)
  let (result, _) ← (do
    let goal ← Lean.Meta.mkFreshExprMVar (Lean.mkConst ``True)
    (((test { elaborator := .anonymous }).run' { goals := [goal.mvarId!] }) {}).run' {}).run' |>.toIO coreCtx coreState
  return result

/-- Create a tactic task: sleep, run tactic, return name. -/
def mkTacticTask (sleepMs : Nat) (tacticStx : Lean.Syntax) (name : String) :
    Lean.Elab.Tactic.TacticM String := do
  IO.sleep sleepMs.toUInt32
  Lean.Elab.Tactic.evalTactic tacticStx
  return name


/-- Test that state is properly threaded through CoreM iteration. -/
def testStateThreading : IO Unit := do
  let (ctx, state) ← mkCoreState #[]

  let testCore : Lean.CoreM (List Nat × List Nat × List String) := do
    -- Tasks that log messages with different delays
    let iter ← Lean.Core.CoreM.parIter [
      do Lean.logInfo "Task 1"; IO.sleep 300; return 1,
      do Lean.logInfo "Task 2"; IO.sleep  50; return 2,
      do Lean.logInfo "Task 3"; IO.sleep 150; return 3
    ]

    -- Map to capture state after each task and collect results
    let results ← (iter.mapM fun result => do
      match result with
      | .ok value =>
        let messages ← Lean.Core.getMessageLog
        let msgs := messages.toList
        let count := msgs.length
        -- Get the message text
        let msgText ← msgs.headD default |>.data.toString
        return (value, count, msgText)
      | .error _ =>
        return (0, 0, "error")).take 3 |>.allowNontermination.toList

    return (results.map (·.1), results.map (·.2.1), results.map (·.2.2))

  let ((values, counts, msgTexts), _) ← testCore.toIO ctx state

  IO.println s!"Values: {values}"
  IO.println s!"Message counts: {counts}"
  IO.println s!"Message texts: {msgTexts}"

/--
info: Values: [1, 2, 3]
Message counts: [1, 1, 1]
Message texts: [Task 1, Task 2, Task 3]
-/
#guard_msgs in
#eval testStateThreading

/-- Test that MetaM.par' returns results in original order. -/
def testMetaMPar : IO Unit := do
  let (ctx, state) ← mkCoreState #[]

  let testMeta : Lean.MetaM (List Nat) := do
    let results ← Lean.Meta.MetaM.par' [
      do IO.sleep 300; return 1,
      do IO.sleep 50; return 2,
      do IO.sleep 150; return 3
    ]
    return results.filterMap (·.toOption)

  let (values, _) ← testMeta.run' |>.toIO ctx state
  IO.println s!"Values in original order: {values}"

/--
info: Values in original order: [1, 2, 3]
-/
#guard_msgs in
#eval testMetaMPar

/-- Test that MetaM.parFirst returns the first successful result. -/
def testMetaMParFirst : IO Unit := do
  let (ctx, state) ← mkCoreState #[]

  let testMeta : Lean.MetaM Nat := do
    Lean.Meta.MetaM.parFirst [
      do IO.sleep 300; Lean.logInfo "Task 1 completed"; return 1,
      do IO.sleep 50; Lean.logInfo "Task 2 completed"; return 2,
      do IO.sleep 150; Lean.logInfo "Task 3 completed"; return 3
    ]

  let (result, finalState) ← testMeta.run' |>.toIO ctx state
  IO.println s!"First result: {result}"

  -- Check message log to see which tasks completed before cancellation
  let messages := finalState.messages.toList
  IO.println s!"Messages logged: {messages.length}"

/--
info: First result: 2
Messages logged: 1
-/
#guard_msgs in
#eval testMetaMParFirst

/-- Test that MetaM.par' properly handles errors. -/
def testMetaMParWithErrors : IO Unit := do
  let (ctx, state) ← mkCoreState #[]

  let testMeta : Lean.MetaM (List String) := do
    let results ← Lean.Meta.MetaM.par' [
      do IO.sleep 100; return "success",
      do IO.sleep 50; throwError "intentional error",
      do IO.sleep 75; return "also success"
    ]
    return results.map fun
      | .ok val => s!"ok: {val}"
      | .error _ => "error"

  let (resultStrings, _) ← testMeta.run' |>.toIO ctx state
  IO.println s!"Results: {resultStrings}"

/--
info: Results: [ok: success, error, ok: also success]
-/
#guard_msgs in
#eval testMetaMParWithErrors

/-- Test that CoreM.par returns state information and restores initial state. -/
def testCoreMParWithState : IO Unit := do
  let (ctx, state) ← mkCoreState #[]

  let testCore : Lean.CoreM (List Nat × Nat) := do
    -- Log initial message
    Lean.logInfo "Initial state"

    let results ← Lean.Core.CoreM.par [
      do Lean.logInfo "Task 1"; IO.sleep 100; return 1,
      do Lean.logInfo "Task 2"; IO.sleep 50; return 2,
      do Lean.logInfo "Task 3"; IO.sleep 75; return 3
    ]

    -- After par, Core.State should be restored to initial (only "Initial state" message)
    let finalMessages ← Lean.Core.getMessageLog
    let finalCount := finalMessages.toList.length

    -- Extract values from results
    let values : List Nat := results.filterMap fun r => match r with
      | .ok (val, _taskState) =>
        some val
      | .error _ => none

    return (values, finalCount)

  let ((values, finalCount), _) ← testCore.toIO ctx state
  IO.println s!"Values: {values}"
  IO.println s!"Final message count (should be 1): {finalCount}"

/--
info: Values: [1, 2, 3]
Final message count (should be 1): 1
-/
#guard_msgs in
#eval testCoreMParWithState

/-- Test that TacticM state is properly threaded through iterations. -/
def testTacticMStateThreading : IO Unit := do
  let tacticTest : Lean.Elab.Tactic.TacticM (List String × List Nat) := do
    let tasks := [
      mkTacticTask 300 (← `(tactic| sorry)) "sorry",
      mkTacticTask 50 (← `(tactic| exact True.intro)) "exact",
      mkTacticTask 150 (← `(tactic| skip)) "skip"
    ]
    let (_, iter) ← Lean.Elab.Tactic.TacticM.parIterWithCancel tasks
    let results ← (iter.mapM fun result =>
      match result with
      | .ok tacticName => return (tacticName, (← Lean.Elab.Tactic.getGoals).length)
      | .error _ => return ("error", 999)).take 3 |>.allowNontermination.toList
    return results.unzip

  let (tacticNames, goalCounts) ← runTacticTest tacticTest

  IO.println s!"Tactic names: {tacticNames}"
  IO.println s!"Goal counts: {goalCounts}"

/--
info: Tactic names: [sorry, exact, skip]
Goal counts: [0, 0, 1]
-/
#guard_msgs in
#eval testTacticMStateThreading

/-- Test that cancellation hooks work properly with cooperative cancellation. -/
def testCancellation : IO Unit := do
  let tacticTest : Lean.Elab.Tactic.TacticM (List String × Nat) := do
    let tasks := [
      mkTacticTask 300  (← `(tactic| sorry)) "sorry",
      mkTacticTask 50   (← `(tactic| exact True.intro)) "exact",
      mkTacticTask 150  (← `(tactic| skip)) "skip",
      mkTacticTask 1000 (← `(tactic| sorry)) "sorry-slow"
    ]
    let (cancel, iter) ← Lean.Elab.Tactic.TacticM.parIterWithCancel tasks

    -- Cancel after 500ms (task4 will still be sleeping)
    IO.sleep 500
    cancel

    -- Consume the iterator and partition into successes and failures
    let results ← iter.take 4 |>.allowNontermination.toList
    let successNames := results.filterMap fun r => match r with | .ok n => some n | .error _ => none
    let failedCount := results.countP fun r => match r with | .error _ => true | _ => false
    return (successNames, failedCount)

  let (successNames, failedCount) ← runTacticTest tacticTest

  -- Sort for deterministic output (timing can vary)
  IO.println s!"Succeeded: {successNames.mergeSort (· < ·)}"
  IO.println s!"Failed: {failedCount}"

/--
info: Succeeded: [exact, skip, sorry]
Failed: 1
-/
#guard_msgs in
#eval testCancellation

/-- Test that parIter runs tasks in parallel AND returns results in original order. -/
def testParIterParallelism : IO Unit := do
  let (ctx, state) ← mkCoreState #[]

  let testCore : Lean.CoreM (List Nat × Nat) := do
    let startTime ← IO.monoMsNow

    -- Three tasks with different sleep times: 300ms, 50ms, 150ms
    -- If parallel: ~300ms total (max)
    -- If sequential: ~500ms total (sum)
    -- Expected order: [1, 2, 3] (original order, not completion order [2, 3, 1])
    let iter ← Lean.Core.CoreM.parIter [
      do IO.sleep 300; return 1,
      do IO.sleep 50; return 2,
      do IO.sleep 150; return 3
    ]

    -- Consume all results from the iterator
    let mut results := []
    for result in iter.allowNontermination do
      match result with
      | .ok value => results := results.concat value
      | .error _ => pure ()

    let endTime ← IO.monoMsNow
    let elapsed := endTime - startTime

    return (results, elapsed)

  let ((results, elapsed), _) ← testCore.toIO ctx state

  IO.println s!"Results: {results}"

  -- Check ordering: should be [1, 2, 3], not [2, 3, 1]
  if results != [1, 2, 3] then
    IO.println s!"FAILED: Expected results in original order [1, 2, 3], got {results}"
  else
    IO.println s!"PASSED: Results in correct original order"

  -- Check parallelism: should be ~300ms, not ~500ms
  if elapsed > 450 then
    IO.println s!"FAILED: Elapsed time >450ms suggests sequential execution!"
  else
    IO.println s!"PASSED: Elapsed time ≤450ms indicates parallel execution"

/--
info: Results: [1, 2, 3]
PASSED: Results in correct original order
PASSED: Elapsed time ≤450ms indicates parallel execution
-/
#guard_msgs in
#eval testParIterParallelism
