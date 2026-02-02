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
        return (0, 0, "error")).take 3 |>.toList

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

  -- Create promises that tasks will resolve after sleeping
  let promise2 ← (IO.Promise.new : BaseIO (IO.Promise Unit))
  let promise3 ← (IO.Promise.new : BaseIO (IO.Promise Unit))

  let testMeta : Lean.MetaM (List (Nat × Bool)) := do
    -- Task 1 sleeps longest, Task 2 shortest - if parallel, Task 2 completes first
    let results ← Lean.Meta.MetaM.par' [
      do IO.sleep 300; let task2Done ← promise2.isResolved; return (1, task2Done),
      do IO.sleep 50; promise2.resolve (); return (2, false),
      do IO.sleep 150; promise3.resolve (); return (3, false)
    ]
    return results.filterMap (·.toOption)

  let (values, _) ← testMeta.run' |>.toIO ctx state
  IO.println s!"Values in original order: {values}"
  -- Task 1 should see that Task 2 completed (promise2 resolved)
  match values with
  | [(1, task2Done), (2, _), (3, _)] =>
    if task2Done then
      IO.println "PASSED: Task 1 observed Task 2 completed (parallel execution verified)"
    else
      IO.println "FAILED: Task 1 did not see Task 2 complete (suggests sequential execution)"
  | _ => IO.println s!"FAILED: Unexpected result structure"

/--
info: Values in original order: [(1, true), (2, false), (3, false)]
PASSED: Task 1 observed Task 2 completed (parallel execution verified)
-/
#guard_msgs in
#eval testMetaMPar

/-- Test that MetaM.parFirst returns the first successful result. -/
def testMetaMParFirst : IO Unit := do
  let (ctx, state) ← mkCoreState #[]

  let testMeta : Lean.MetaM Nat := do
    -- Task 2 sleeps least, so should complete first and be returned
    Lean.Meta.MetaM.parFirst [
      do IO.sleep 300; Lean.logInfo "Task 1 completed"; return 1,
      do IO.sleep 50; Lean.logInfo "Task 2 completed"; return 2,
      do IO.sleep 150; Lean.logInfo "Task 3 completed"; return 3
    ]

  let (result, finalState) ← testMeta.run' |>.toIO ctx state
  IO.println s!"First result: {result}"

  -- Check message log - only the first completing task should have logged
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
      | .error _ => return ("error", 999)).take 3 |>.toList
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

/-- Test that TacticM parallel execution works correctly. -/
def testTacticMParallel : IO Unit := do
  -- Create promise that fastest task will resolve
  let promise ← (IO.Promise.new : BaseIO (IO.Promise Unit))

  let tacticTest : Lean.Elab.Tactic.TacticM (List (String × Bool)) := do
    let tasks := [
      -- Task 1 sleeps longest, should see Task 2 completed
      do IO.sleep 300; Lean.Elab.Tactic.evalTactic (← `(tactic| sorry));
         let task2Done ← promise.isResolved; return ("sorry", task2Done),
      -- Task 2 sleeps shortest, completes first
      do IO.sleep 50; Lean.Elab.Tactic.evalTactic (← `(tactic| exact True.intro));
         promise.resolve (); return ("exact", false),
      do IO.sleep 150; Lean.Elab.Tactic.evalTactic (← `(tactic| skip));
         return ("skip", false)
    ]
    let (_, iter) ← Lean.Elab.Tactic.TacticM.parIterWithCancel tasks

    -- Consume the iterator and collect successful results
    let results ← iter.take 3 |>.toList
    return results.filterMap fun r => match r with | .ok n => some n | .error _ => none

  let successResults ← runTacticTest tacticTest

  IO.println s!"Results: {successResults}"
  -- Check if Task 1 observed Task 2 completed
  match successResults with
  | [("sorry", task2Done), ("exact", _), ("skip", _)] =>
    if task2Done then
      IO.println "PASSED: Task 1 observed Task 2 completed (parallel execution verified)"
    else
      IO.println "FAILED: Task 1 did not see Task 2 complete (suggests sequential execution)"
  | _ => IO.println s!"FAILED: Unexpected result structure"

/--
info: Results: [(sorry, true), (exact, false), (skip, false)]
PASSED: Task 1 observed Task 2 completed (parallel execution verified)
-/
#guard_msgs in
#eval testTacticMParallel

/-- Test that parIter returns results in original order (not completion order). -/
def testParIterOrdering : IO Unit := do
  let (ctx, state) ← mkCoreState #[]

  -- Create promises that tasks will resolve after sleeping
  let promise2 ← (IO.Promise.new : BaseIO (IO.Promise Unit))
  let promise3 ← (IO.Promise.new : BaseIO (IO.Promise Unit))

  let testCore : Lean.CoreM (List (Nat × Bool)) := do
    -- Task 1 sleeps longest, Task 2 shortest - verify parallel execution and original ordering
    let iter ← Lean.Core.CoreM.parIter [
      do IO.sleep 300; let task2Done ← promise2.isResolved; return (1, task2Done),
      do IO.sleep 50; promise2.resolve (); return (2, false),
      do IO.sleep 150; promise3.resolve (); return (3, false)
    ]

    -- Consume all results from the iterator
    let mut results := []
    for result in iter do
      match result with
      | .ok value => results := results.concat value
      | .error _ => pure ()

    return results

  let (results, _) ← testCore.toIO ctx state

  IO.println s!"Results: {results}"

  -- Check ordering: should be [(1, true), (2, false), (3, false)] - original order with Task 1 seeing Task 2 done
  match results with
  | [(1, task2Done), (2, _), (3, _)] =>
    if task2Done then
      IO.println "PASSED: Results in original order AND Task 1 observed Task 2 completed (parallel execution verified)"
    else
      IO.println "FAILED: Results in order but Task 1 did not see Task 2 complete (suggests sequential execution)"
  | _ => IO.println s!"FAILED: Unexpected result structure or ordering: {results}"

/--
info: Results: [(1, true), (2, false), (3, false)]
PASSED: Results in original order AND Task 1 observed Task 2 completed (parallel execution verified)
-/
#guard_msgs in
#eval testParIterOrdering
