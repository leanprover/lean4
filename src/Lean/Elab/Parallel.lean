/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
public import Lean.Elab.Task
import Init.System.IO

/-!
# Iterator-based parallelization for Lean's tactic monads.

This file provides utilities for running computations in parallel using Lean's task system,
with support for collecting results in different ways.

## Main functions

For each monad (`IO`, `CoreM`, `MetaM`, `TermElabM`, `TacticM`), the following functions are provided:

- `par` / `par'`
  - Run jobs in parallel, collect results in original order
  - Takes `List (MonadM α)`, returns `MonadM (List (Except Error (α × State)))` / `MonadM (List (Except Error α))`
  - All tasks run in parallel, results returned in input order
  - `par` returns state information, `par'` discards state
  - Final state is restored to initial state (before tasks ran)
  - Errors wrapped in `Except` so all results are collected

- `parIter` / `parIterWithCancel`
  - Run jobs in parallel, iterate over results in original order
  - Takes `List (MonadM α)`, returns iterator
  - `parIterWithCancel` also returns cancellation hook

- `parIterGreedy` / `parIterGreedyWithCancel`
  - Run jobs in parallel, iterate over results in completion order (greedily)
  - Takes `List (MonadM α)`, returns iterator
  - `parIterGreedyWithCancel` also returns cancellation hook

- `parFirst`
  - Run jobs in parallel, return first successful result (by completion order)
  - Cancels remaining tasks after first success (by default)
  - Throws error if all tasks fail

## Implementation notes

The greedy iterator-based functions use `IO.waitAny'` internally to wait for task completion in any order.
The ordered iterator-based functions process tasks sequentially in the original order.

**State threading in iterators:**
The iterators (`parIter`, `parIterGreedy`, and their `WithCancel` variants) preserve state from each
completed task. When you map over an iterator with a monadic function, the monad state will be that at
the conclusion of the monadic action that produced each value. This means:
- For `parIter`: State is threaded sequentially in the original task order
- For `parIterGreedy`: State is threaded in task completion order

This allows you to observe state changes (like logged messages, modified metavariable contexts, etc.)
as tasks complete, unlike `par`/`par'` which restore the initial state after collecting all results.

Iterators do not have `Finite` instances, as we cannot prove termination from the available
information. For consumers that require `Finite` (like `.toList`), use `.allowNontermination.toList`.

## Chunking support

The `par`, `par'`, `parIter`, and `parIterWithCancel` functions support optional chunking to reduce
task creation overhead when there are many small jobs. Pass `maxTasks` to limit the number of parallel
tasks created; jobs will be grouped into chunks that run sequentially within each task.

- `maxTasks = 0` (default): No chunking, one task per job (original behavior)
- `maxTasks > 0`: Auto-compute chunk size to limit task count
- `minChunkSize`: Minimum jobs per chunk (default 1)

Example: With 1000 jobs and `maxTasks := 128, minChunkSize := 8`, chunk size = 8, creating ~125 tasks.
-/

/-- Split a list into chunks of at most `chunkSize` elements. -/
def toChunks {α : Type} (xs : List α) (chunkSize : Nat) : List (List α) :=
  if h : chunkSize ≤ 1 then xs.map ([·])
  else go xs [] (Nat.lt_of_not_le h)
where
  go (remaining : List α) (acc : List (List α)) (hc : 1 < chunkSize) : List (List α) :=
    if _h : remaining.length ≤ chunkSize then
      (remaining :: acc).reverse
    else
      go (remaining.drop chunkSize) (remaining.take chunkSize :: acc) hc
  termination_by remaining.length
  decreasing_by simp_wf; omega

/-- Compute chunk size given job count, max tasks, and minimum chunk size. -/
def computeChunkSize (numJobs maxTasks minChunkSize : Nat) : Nat :=
  if maxTasks = 0 then 1
  else max minChunkSize ((numJobs + maxTasks - 1) / maxTasks)

public section

namespace Std.Iterators

/--
Internal state for an iterator over tasks.
Maintains the list of tasks that haven't completed yet.
-/
structure TaskIterator (α : Type w) where
  private tasks : List (Task α)

private instance {α : Type} : Iterator (TaskIterator α) BaseIO α where
  IsPlausibleStep it
    | .yield it' out => True
    | .skip _ => False
    | .done => it.internalState.tasks = []
  step it := do
    match h : it.internalState.tasks with
    | [] =>
        pure <| .deflate ⟨.done, rfl⟩
    | task :: rest =>
        have hlen : 0 < (task :: rest).length := by simp
        let (result, remaining) ← IO.waitAny' (task :: rest) hlen
        pure <| .deflate ⟨
          .yield (Std.Iterators.toIterM { tasks := remaining } BaseIO α) result,
          trivial⟩

end Std.Iterators

namespace IO

open Std.Iterators

/--
Creates an iterator over a list of tasks that yields results in completion order.

Uses `IO.waitAny'` to wait for the next task to complete (whichever finishes first),
then yields that result and continues with the remaining tasks.

The iterator will terminate once all tasks have completed, but we don't provide a `Finite`
instance since we cannot prove termination from the available information.
In practice, if all tasks eventually complete, the iterator will be finite.

## Example
```lean
let tasks : List (Task Nat) ← [
  IO.asTask (pure 1),
  IO.asTask (pure 2),
  IO.asTask (pure 3)
]
let iter := IO.iterTasks tasks
for result in iter do
  IO.println s!"Got result: {result}"
```
-/
private def iterTasks {α : Type} (tasks : List (Task α)) : IterM (α := TaskIterator α) BaseIO α :=
  Std.Iterators.toIterM { tasks } BaseIO α

end IO

namespace Lean.Core.CoreM

open Std.Iterators

/--
Runs a list of CoreM computations in parallel and returns:
* a combined cancellation hook for all tasks, and
* an iterator that yields results in original order.

The iterator runs in CoreM, and as it yields each result, it updates the CoreM state
to reflect the state when that particular task completed. This means the state is
threaded through the iteration in the order of the original list.

Results are wrapped in `Except Exception α` so that errors in individual tasks don't stop
the iteration - you can observe all results including which tasks failed.

The iterator will terminate after all jobs complete (assuming they all do complete).
-/
def parIterWithCancel {α : Type} (jobs : List (CoreM α)) := do
  let (cancels, tasks) := (← jobs.mapM asTask).unzip
  let combinedCancel := cancels.forM id
  let iterWithErrors := tasks.iter.mapM fun (task : Task (CoreM α)) => do
    try
      let result ← task.get
      pure (Except.ok result)
    catch e =>
      pure (Except.error e)
  return (combinedCancel, iterWithErrors)

/--
Runs a list of CoreM computations in parallel (without cancellation hook).

Returns an iterator that yields results in original order, wrapped in `Except Exception α`.
-/
def parIter {α : Type} (jobs : List (CoreM α)) :=
  (·.2) <$> parIterWithCancel jobs

/--
Runs a list of CoreM computations in parallel and returns:
* a combined cancellation hook for all tasks, and
* an iterator that yields results in completion order (greedily).

The iterator runs in CoreM, and as it yields each result, it updates the CoreM state
to reflect the state when that particular task completed. This means the state is
threaded through the iteration in task completion order.

Results are wrapped in `Except Exception α` so that errors in individual tasks don't stop
the iteration - you can observe all results including which tasks failed.

The iterator will terminate after all jobs complete (assuming they all do complete).
-/
def parIterGreedyWithCancel {α : Type} (jobs : List (CoreM α)) := do
  let (cancels, tasks) := (← jobs.mapM asTask).unzip
  let combinedCancel := cancels.forM id
  let baseIter := IO.iterTasks tasks
  -- mapM with error handling - execute each task and catch errors
  let iterWithErrors := baseIter.mapM fun taskMonadic => do
    try
      pure (Except.ok (← taskMonadic))
    catch e =>
      pure (Except.error e)
  return (combinedCancel, iterWithErrors)

/--
Runs a list of CoreM computations in parallel (without cancellation hook).

Returns an iterator that yields results in completion order, wrapped in `Except Exception α`.
-/
def parIterGreedy {α : Type} (jobs : List (CoreM α)) :=
  (·.2) <$> parIterGreedyWithCancel jobs

/-- Internal: run jobs in parallel without chunking, returning state. -/
private def parCore {α : Type} (jobs : List (CoreM α)) :
    CoreM (List (Except Exception (α × Core.SavedState))) := do
  let initialState ← get
  let tasks ← jobs.mapM asTask'
  let mut results := []
  for task in tasks do
    let resultWithState ← observing do
      let result ← task.get
      pure (result, (← saveState))
    results := resultWithState :: results
  set initialState
  return results.reverse

/--
Runs a list of CoreM computations in parallel and collects results in the original order,
including the saved state after each task completes.

Unlike `parIter`, this waits for all tasks to complete and returns results
in the same order as the input list, not in completion order.

Results are wrapped in `Except Exception (α × Core.SavedState)` so that errors in individual
tasks don't stop the collection - you can observe all results including which tasks failed.

The final CoreM state is restored to the initial state (before tasks ran).

**Chunking:** Pass `maxTasks > 0` to limit parallel tasks by grouping jobs into chunks.
-/
def par {α : Type} (jobs : List (CoreM α))
    (maxTasks : Nat := 0) (minChunkSize : Nat := 1) :
    CoreM (List (Except Exception (α × Core.SavedState))) := do
  let chunkSize := computeChunkSize jobs.length maxTasks minChunkSize
  if chunkSize ≤ 1 then
    parCore jobs
  else
    let initialState ← get
    let chunks := toChunks jobs chunkSize
    let chunkJobs := chunks.map fun chunk => do
      let mut results := []
      for job in chunk do
        let r ← observing do
          let a ← job
          pure (a, ← saveState)
        results := r :: results
      pure results.reverse
    let chunkResults ← parCore chunkJobs
    set initialState
    let mut allResults := []
    for chunkResult in chunkResults do
      match chunkResult with
      | .ok (jobResults, _) => allResults := allResults ++ jobResults
      | .error e => allResults := allResults ++ [.error e]
    return allResults

/-- Internal: run jobs in parallel without chunking, discarding state. -/
private def parCore' {α : Type} (jobs : List (CoreM α)) :
    CoreM (List (Except Exception α)) := do
  let initialState ← get
  let tasks ← jobs.mapM asTask'
  let mut results := []
  for task in tasks do
    try
      let result ← task.get
      results := .ok result :: results
    catch e =>
      results := .error e :: results
  set initialState
  return results.reverse

/--
Runs a list of CoreM computations in parallel and collects results in the original order,
discarding state information.

Unlike `par`, this doesn't return state information from tasks.

The final CoreM state is restored to the initial state (before tasks ran).

**Chunking:** Pass `maxTasks > 0` to limit parallel tasks by grouping jobs into chunks.
-/
def par' {α : Type} (jobs : List (CoreM α))
    (maxTasks : Nat := 0) (minChunkSize : Nat := 1) :
    CoreM (List (Except Exception α)) := do
  let chunkSize := computeChunkSize jobs.length maxTasks minChunkSize
  if chunkSize ≤ 1 then
    parCore' jobs
  else
    let initialState ← get
    let chunks := toChunks jobs chunkSize
    let chunkJobs := chunks.map fun chunk => do
      let mut results := []
      for job in chunk do
        let r ← observing job
        results := r :: results
      pure results.reverse
    let chunkResults ← parCore' chunkJobs
    set initialState
    let mut allResults := []
    for chunkResult in chunkResults do
      match chunkResult with
      | .ok jobResults => allResults := allResults ++ jobResults
      | .error e => allResults := allResults ++ [.error e]
    return allResults

/--
Runs a list of CoreM computations in parallel and returns the first successful result
(by completion order, not list order).

If `cancel := true` (the default), cancels all remaining tasks after the first success.
-/
def parFirst {α : Type} (jobs : List (CoreM α)) (cancel : Bool := true) : CoreM α := do
  let (cancelHook, iter) ← parIterGreedyWithCancel jobs
  for result in iter.allowNontermination do
    match result with
    | .ok value =>
      if cancel then cancelHook
      return value
    | .error _ => continue
  throwError "All parallel tasks failed"

end Lean.Core.CoreM

namespace Lean.Meta.MetaM

open Std.Iterators

/-- Internal: run jobs in parallel without chunking, returning state. -/
private def parCore {α : Type} (jobs : List (MetaM α)) :
    MetaM (List (Except Exception (α × Meta.SavedState))) := do
  let initialState ← get
  let tasks ← jobs.mapM asTask'
  let mut results := []
  for task in tasks do
    let resultWithState ← observing do
      let result ← task.get
      pure (result, (← saveState))
    results := resultWithState :: results
  set initialState
  return results.reverse

/-- Internal: run jobs in parallel without chunking, discarding state. -/
private def parCore' {α : Type} (jobs : List (MetaM α)) :
    MetaM (List (Except Exception α)) := do
  let initialState ← get
  let tasks ← jobs.mapM asTask'
  let mut results := []
  for task in tasks do
    try
      let result ← task.get
      results := .ok result :: results
    catch e =>
      results := .error e :: results
  set initialState
  return results.reverse

/--
Runs a list of MetaM computations in parallel and collects results in the original order,
including the saved state after each task completes.

Unlike `parIter`, this waits for all tasks to complete and returns results
in the same order as the input list, not in completion order.

Results are wrapped in `Except Exception (α × Meta.SavedState)` so that errors in individual
tasks don't stop the collection - you can observe all results including which tasks failed.

The final MetaM state is restored to the initial state (before tasks ran).

**Chunking:** Pass `maxTasks > 0` to limit parallel tasks by grouping jobs into chunks.
-/
def par {α : Type} (jobs : List (MetaM α))
    (maxTasks : Nat := 0) (minChunkSize : Nat := 1) :
    MetaM (List (Except Exception (α × Meta.SavedState))) := do
  let chunkSize := computeChunkSize jobs.length maxTasks minChunkSize
  if chunkSize ≤ 1 then
    parCore jobs
  else
    let initialState ← get
    let chunks := toChunks jobs chunkSize
    let chunkJobs := chunks.map fun chunk => do
      let mut results := []
      for job in chunk do
        let r ← observing do
          let a ← job
          pure (a, ← saveState)
        results := r :: results
      pure results.reverse
    let chunkResults ← parCore chunkJobs
    set initialState
    let mut allResults := []
    for chunkResult in chunkResults do
      match chunkResult with
      | .ok (jobResults, _) => allResults := allResults ++ jobResults
      | .error e => allResults := allResults ++ [.error e]
    return allResults

/--
Runs a list of MetaM computations in parallel and collects results in the original order,
discarding state information.

Unlike `par`, this doesn't return state information from tasks.

The final MetaM state is restored to the initial state (before tasks ran).

**Chunking:** Pass `maxTasks > 0` to limit parallel tasks by grouping jobs into chunks.
-/
def par' {α : Type} (jobs : List (MetaM α))
    (maxTasks : Nat := 0) (minChunkSize : Nat := 1) :
    MetaM (List (Except Exception α)) := do
  let chunkSize := computeChunkSize jobs.length maxTasks minChunkSize
  if chunkSize ≤ 1 then
    parCore' jobs
  else
    let initialState ← get
    let chunks := toChunks jobs chunkSize
    let chunkJobs := chunks.map fun chunk => do
      let mut results := []
      for job in chunk do
        let r ← observing job
        results := r :: results
      pure results.reverse
    let chunkResults ← parCore' chunkJobs
    set initialState
    let mut allResults := []
    for chunkResult in chunkResults do
      match chunkResult with
      | .ok jobResults => allResults := allResults ++ jobResults
      | .error e => allResults := allResults ++ [.error e]
    return allResults

/--
Runs a list of MetaM computations in parallel and returns:
* a combined cancellation hook for all tasks, and
* an iterator that yields results in original order.

The iterator runs in MetaM, and as it yields each result, it updates the MetaM state
to reflect the state when that particular task completed. This means the state is
threaded through the iteration in the order of the original list.

Results are wrapped in `Except Exception α` so that errors in individual tasks don't stop
the iteration - you can observe all results including which tasks failed.

The iterator will terminate after all jobs complete (assuming they all do complete).
-/
def parIterWithCancel {α : Type} (jobs : List (MetaM α)) := do
  let (cancels, tasks) := (← jobs.mapM asTask).unzip
  let combinedCancel := cancels.forM id
  -- Create iterator that processes tasks sequentially
  let iterWithErrors := tasks.iter.mapM fun (task : Task (MetaM α)) => do
    try
      let result ← task.get
      pure (Except.ok result)
    catch e =>
      pure (Except.error e)
  return (combinedCancel, iterWithErrors)

/--
Runs a list of MetaM computations in parallel (without cancellation hook).

Returns an iterator that yields results in original order, wrapped in `Except Exception α`.
-/
def parIter {α : Type} (jobs : List (MetaM α)) :=
  (·.2) <$> parIterWithCancel jobs

/--
Runs a list of MetaM computations in parallel and returns:
* a combined cancellation hook for all tasks, and
* an iterator that yields results in completion order (greedily).

The iterator runs in MetaM, and as it yields each result, it updates the MetaM state
to reflect the state when that particular task completed. This means the state is
threaded through the iteration in task completion order.

Results are wrapped in `Except Exception α` so that errors in individual tasks don't stop
the iteration - you can observe all results including which tasks failed.

The iterator will terminate after all jobs complete (assuming they all do complete).
-/
def parIterGreedyWithCancel {α : Type} (jobs : List (MetaM α)) := do
  let (cancels, tasks) := (← jobs.mapM asTask).unzip
  let combinedCancel := cancels.forM id
  let baseIter := IO.iterTasks tasks
  -- mapM with error handling - execute each task and catch errors
  let iterWithErrors := baseIter.mapM fun taskMonadic => do
    try
      pure (Except.ok (← taskMonadic))
    catch e =>
      pure (Except.error e)
  return (combinedCancel, iterWithErrors)

/--
Runs a list of MetaM computations in parallel (without cancellation hook).

Returns an iterator that yields results in completion order, wrapped in `Except Exception α`.
-/
def parIterGreedy {α : Type} (jobs : List (MetaM α)) :=
  (·.2) <$> parIterGreedyWithCancel jobs

/--
Runs a list of MetaM computations in parallel and returns the first successful result
(by completion order, not list order).

If `cancel := true` (the default), cancels all remaining tasks after the first success.
-/
def parFirst {α : Type} (jobs : List (MetaM α)) (cancel : Bool := true) : MetaM α := do
  let (cancelHook, iter) ← parIterGreedyWithCancel jobs
  for result in iter.allowNontermination do
    match result with
    | .ok value =>
      if cancel then cancelHook
      return value
    | .error _ => continue
  throwError "All parallel tasks failed"

end Lean.Meta.MetaM

namespace Lean.Elab.Term.TermElabM

open Std.Iterators

/--
Runs a list of TermElabM computations in parallel and returns:
* a combined cancellation hook for all tasks, and
* an iterator that yields results in original order.

The iterator runs in TermElabM, and as it yields each result, it updates the TermElabM state
to reflect the state when that particular task completed. This means the state is
threaded through the iteration in the order of the original list.

Results are wrapped in `Except Exception α` so that errors in individual tasks don't stop
the iteration - you can observe all results including which tasks failed.

The iterator will terminate after all jobs complete (assuming they all do complete).
-/
def parIterWithCancel {α : Type} (jobs : List (TermElabM α)) := do
  let (cancels, tasks) := (← jobs.mapM asTask).unzip
  let combinedCancel := cancels.forM id
  -- Create iterator that processes tasks sequentially
  let iterWithErrors := tasks.iter.mapM fun (task : Task (TermElabM α)) => do
    try
      let result ← task.get
      pure (Except.ok result)
    catch e =>
      pure (Except.error e)
  return (combinedCancel, iterWithErrors)

/--
Runs a list of TermElabM computations in parallel (without cancellation hook).

Returns an iterator that yields results in original order, wrapped in `Except Exception α`.
-/
def parIter {α : Type} (jobs : List (TermElabM α)) :=
  (·.2) <$> parIterWithCancel jobs

/--
Runs a list of TermElabM computations in parallel and returns:
* a combined cancellation hook for all tasks, and
* an iterator that yields results in completion order (greedily).

The iterator runs in TermElabM, and as it yields each result, it updates the TermElabM state
to reflect the state when that particular task completed. This means the state is
threaded through the iteration in task completion order.

Results are wrapped in `Except Exception α` so that errors in individual tasks don't stop
the iteration - you can observe all results including which tasks failed.

The iterator will terminate after all jobs complete (assuming they all do complete).
-/
def parIterGreedyWithCancel {α : Type} (jobs : List (TermElabM α)) := do
  let (cancels, tasks) := (← jobs.mapM asTask).unzip
  let combinedCancel := cancels.forM id
  let baseIter := IO.iterTasks tasks
  -- mapM with error handling - execute each task and catch errors
  let iterWithErrors := baseIter.mapM fun taskMonadic => do
    try
      pure (Except.ok (← taskMonadic))
    catch e =>
      pure (Except.error e)
  return (combinedCancel, iterWithErrors)

/--
Runs a list of TermElabM computations in parallel (without cancellation hook).

Returns an iterator that yields results in completion order, wrapped in `Except Exception α`.
-/
def parIterGreedy {α : Type} (jobs : List (TermElabM α)) :=
  (·.2) <$> parIterGreedyWithCancel jobs

/-- Internal: run jobs in parallel without chunking, returning state. -/
private def parCore {α : Type} (jobs : List (TermElabM α)) :
    TermElabM (List (Except Exception (α × Term.SavedState))) := do
  let initialState ← get
  let tasks ← jobs.mapM asTask'
  let mut results := []
  for task in tasks do
    try
      let result ← task.get
      let taskState ← saveState
      results := .ok (result, taskState) :: results
    catch e =>
      results := .error e :: results
  set initialState
  return results.reverse

/-- Internal: run jobs in parallel without chunking, discarding state. -/
private def parCore' {α : Type} (jobs : List (TermElabM α)) :
    TermElabM (List (Except Exception α)) := do
  let initialState ← get
  let tasks ← jobs.mapM asTask'
  let mut results := []
  for task in tasks do
    try
      let result ← task.get
      results := .ok result :: results
    catch e =>
      results := .error e :: results
  set initialState
  return results.reverse

/--
Runs a list of TermElabM computations in parallel and collects results in the original order,
including the saved state after each task completes.

Unlike `parIter`, this waits for all tasks to complete and returns results
in the same order as the input list, not in completion order.

Results are wrapped in `Except Exception (α × Term.SavedState)` so that errors in individual
tasks don't stop the collection - you can observe all results including which tasks failed.

The final TermElabM state is restored to the initial state (before tasks ran).

**Chunking:** Pass `maxTasks > 0` to limit parallel tasks by grouping jobs into chunks.
-/
def par {α : Type} (jobs : List (TermElabM α))
    (maxTasks : Nat := 0) (minChunkSize : Nat := 1) :
    TermElabM (List (Except Exception (α × Term.SavedState))) := do
  let chunkSize := computeChunkSize jobs.length maxTasks minChunkSize
  if chunkSize ≤ 1 then
    parCore jobs
  else
    let initialState ← get
    let chunks := toChunks jobs chunkSize
    -- Each chunk processes its jobs sequentially, collecting Except results
    let chunkJobs := chunks.map fun chunk => do
      let mut results : List (Except Exception (α × Term.SavedState)) := []
      for job in chunk do
        try
          let a ← job
          let s ← saveState
          results := .ok (a, s) :: results
        catch e =>
          results := .error e :: results
      pure results.reverse
    let chunkResults ← parCore' chunkJobs
    set initialState
    let mut allResults := []
    for chunkResult in chunkResults do
      match chunkResult with
      | .ok jobResults => allResults := allResults ++ jobResults
      | .error e => allResults := allResults ++ [.error e]
    return allResults

/--
Runs a list of TermElabM computations in parallel and collects results in the original order,
discarding state information.

Unlike `par`, this doesn't return state information from tasks.

The final TermElabM state is restored to the initial state (before tasks ran).

**Chunking:** Pass `maxTasks > 0` to limit parallel tasks by grouping jobs into chunks.
-/
def par' {α : Type} (jobs : List (TermElabM α))
    (maxTasks : Nat := 0) (minChunkSize : Nat := 1) :
    TermElabM (List (Except Exception α)) := do
  let chunkSize := computeChunkSize jobs.length maxTasks minChunkSize
  if chunkSize ≤ 1 then
    parCore' jobs
  else
    let initialState ← get
    let chunks := toChunks jobs chunkSize
    let chunkJobs := chunks.map fun chunk => do
      let mut results : List (Except Exception α) := []
      for job in chunk do
        try
          let a ← job
          results := .ok a :: results
        catch e =>
          results := .error e :: results
      pure results.reverse
    let chunkResults ← parCore' chunkJobs
    set initialState
    let mut allResults := []
    for chunkResult in chunkResults do
      match chunkResult with
      | .ok jobResults => allResults := allResults ++ jobResults
      | .error e => allResults := allResults ++ [.error e]
    return allResults

/--
Runs a list of TermElabM computations in parallel and returns the first successful result
(by completion order, not list order).

If `cancel := true` (the default), cancels all remaining tasks after the first success.
-/
def parFirst {α : Type} (jobs : List (TermElabM α)) (cancel : Bool := true) : TermElabM α := do
  let (cancelHook, iter) ← parIterGreedyWithCancel jobs
  for result in iter.allowNontermination do
    match result with
    | .ok value =>
      if cancel then cancelHook
      return value
    | .error _ => continue
  throwError "All parallel tasks failed"

end Lean.Elab.Term.TermElabM

namespace Lean.Elab.Tactic.TacticM

open Std.Iterators

/--
Runs a list of TacticM computations in parallel and returns:
* a combined cancellation hook for all tasks, and
* an iterator that yields results in original order.

The iterator runs in TacticM, and as it yields each result, it updates the TacticM state
to reflect the state when that particular task completed. This means the state is
threaded through the iteration in the order of the original list.

Results are wrapped in `Except Exception α` so that errors in individual tasks don't stop
the iteration - you can observe all results including which tasks failed.

The iterator will terminate after all jobs complete (assuming they all do complete).
-/
def parIterWithCancel {α : Type} (jobs : List (TacticM α)) := do
  let (cancels, tasks) := (← jobs.mapM asTask).unzip
  let combinedCancel := cancels.forM id
  -- Create iterator that processes tasks sequentially
  let iterWithErrors := tasks.iter.mapM fun (task : Task (TacticM α)) => do
    try
      let result ← task.get
      pure (Except.ok result)
    catch e =>
      pure (Except.error e)
  return (combinedCancel, iterWithErrors)

/--
Runs a list of TacticM computations in parallel (without cancellation hook).

Returns an iterator that yields results in original order, wrapped in `Except Exception α`.
-/
def parIter {α : Type} (jobs : List (TacticM α)) :=
  (·.2) <$> parIterWithCancel jobs

/--
Runs a list of TacticM computations in parallel and returns:
* a combined cancellation hook for all tasks, and
* an iterator that yields results in completion order (greedily).

The iterator runs in TacticM, and as it yields each result, it updates the TacticM state
to reflect the state when that particular task completed. This means the state is
threaded through the iteration in task completion order.

Results are wrapped in `Except Exception α` so that errors in individual tasks don't stop
the iteration - you can observe all results including which tasks failed.

The iterator will terminate after all jobs complete (assuming they all do complete).
-/
def parIterGreedyWithCancel {α : Type} (jobs : List (TacticM α)) := do
  let (cancels, tasks) := (← jobs.mapM asTask).unzip
  let combinedCancel := cancels.forM id
  let baseIter := IO.iterTasks tasks
  -- mapM with error handling - execute each task and catch errors
  let iterWithErrors := baseIter.mapM fun taskMonadic => do
    try
      pure (Except.ok (← taskMonadic))
    catch e =>
      pure (Except.error e)
  return (combinedCancel, iterWithErrors)

/--
Runs a list of TacticM computations in parallel (without cancellation hook).

Returns an iterator that yields results in completion order, wrapped in `Except Exception α`.
-/
def parIterGreedy {α : Type} (jobs : List (TacticM α)) :=
  (·.2) <$> parIterGreedyWithCancel jobs

/-- Internal: run jobs in parallel without chunking, returning state. -/
private def parCore {α : Type} (jobs : List (TacticM α)) :
    TacticM (List (Except Exception (α × Tactic.SavedState))) := do
  let initialState ← get
  let tasks ← jobs.mapM asTask'
  let mut results := []
  for task in tasks do
    try
      let result ← task.get
      let taskState ← Tactic.saveState
      results := .ok (result, taskState) :: results
    catch e =>
      results := .error e :: results
  set initialState
  return results.reverse

/-- Internal: run jobs in parallel without chunking, discarding state. -/
private def parCore' {α : Type} (jobs : List (TacticM α)) :
    TacticM (List (Except Exception α)) := do
  let initialState ← get
  let tasks ← jobs.mapM asTask'
  let mut results := []
  for task in tasks do
    try
      let result ← task.get
      results := .ok result :: results
    catch e =>
      results := .error e :: results
  set initialState
  return results.reverse

/--
Runs a list of TacticM computations in parallel and collects results in the original order,
including the saved state after each task completes.

Unlike `parIter`, this waits for all tasks to complete and returns results
in the same order as the input list, not in completion order.

Results are wrapped in `Except Exception (α × Tactic.SavedState)` so that errors in individual
tasks don't stop the collection - you can observe all results including which tasks failed.

The final TacticM state is restored to the initial state (before tasks ran).

**Chunking:** Pass `maxTasks > 0` to limit parallel tasks by grouping jobs into chunks.
-/
def par {α : Type} (jobs : List (TacticM α))
    (maxTasks : Nat := 0) (minChunkSize : Nat := 1) :
    TacticM (List (Except Exception (α × Tactic.SavedState))) := do
  let chunkSize := computeChunkSize jobs.length maxTasks minChunkSize
  if chunkSize ≤ 1 then
    parCore jobs
  else
    let initialState ← get
    let chunks := toChunks jobs chunkSize
    -- Each chunk processes its jobs sequentially, collecting Except results
    let chunkJobs := chunks.map fun chunk => do
      let mut results : List (Except Exception (α × Tactic.SavedState)) := []
      for job in chunk do
        try
          let a ← job
          let s ← Tactic.saveState
          results := .ok (a, s) :: results
        catch e =>
          results := .error e :: results
      pure results.reverse
    let chunkResults ← parCore' chunkJobs
    set initialState
    let mut allResults := []
    for chunkResult in chunkResults do
      match chunkResult with
      | .ok jobResults => allResults := allResults ++ jobResults
      | .error e => allResults := allResults ++ [.error e]
    return allResults

/--
Runs a list of TacticM computations in parallel and collects results in the original order,
discarding state information.

Unlike `par`, this doesn't return state information from tasks.

The final TacticM state is restored to the initial state (before tasks ran).

**Chunking:** Pass `maxTasks > 0` to limit parallel tasks by grouping jobs into chunks.
-/
def par' {α : Type} (jobs : List (TacticM α))
    (maxTasks : Nat := 0) (minChunkSize : Nat := 1) :
    TacticM (List (Except Exception α)) := do
  let chunkSize := computeChunkSize jobs.length maxTasks minChunkSize
  if chunkSize ≤ 1 then
    parCore' jobs
  else
    let initialState ← get
    let chunks := toChunks jobs chunkSize
    let chunkJobs := chunks.map fun chunk => do
      let mut results : List (Except Exception α) := []
      for job in chunk do
        try
          let a ← job
          results := .ok a :: results
        catch e =>
          results := .error e :: results
      pure results.reverse
    let chunkResults ← parCore' chunkJobs
    set initialState
    let mut allResults := []
    for chunkResult in chunkResults do
      match chunkResult with
      | .ok jobResults => allResults := allResults ++ jobResults
      | .error e => allResults := allResults ++ [.error e]
    return allResults

/--
Runs a list of TacticM computations in parallel and returns the first successful result
(by completion order, not list order).

If `cancel := true` (the default), cancels all remaining tasks after the first success.
-/
def parFirst {α : Type} (jobs : List (TacticM α)) (cancel : Bool := true) : TacticM α := do
  let (cancelHook, iter) ← parIterGreedyWithCancel jobs
  for result in iter.allowNontermination do
    match result with
    | .ok value =>
      if cancel then cancelHook
      return value
    | .error _ => continue
  throwError "All parallel tasks failed"

end Lean.Elab.Tactic.TacticM
