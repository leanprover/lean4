/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
public import Lean.Elab.Tactic.Basic

/-!
# Task creation utilities for Lean's tactic monads.

This file provides `asTask` and `asTask'` functions for various monads
(`CoreM`, `MetaM`, `TermElabM`, `TacticM`), which convert monadic computations
into tasks that run in parallel while preserving state.

Each `asTask` function returns:
* a cancellation hook and
* a `Task` containing a monadic value with the cached result and updated state

The `asTask'` variants omit the cancellation hook for convenience.

Note: Calling `IO.cancel` on `t.map f` does not cancel `t`,
so these functions are careful to construct cancellation hooks
connected to the underlying task rather than various maps of it.
-/

public section

namespace Lean.Core.CoreM

/--
Given a monadic value in `CoreM`, creates a task that runs it in the current state,
returning
* a cancellation hook and
* a monadic value with the cached result (and subsequent state as it was after running).

The task is run with a fresh `CancelToken` in its context, so it can detect cancellation
via `Core.checkInterrupted`. The cancellation hook sets this token.

Uses `Core.wrapAsync` internally to properly handle name generators and heartbeats.

Note: We only set the cancel token and don't call `IO.cancel task`. We're uncertain whether
`IO.cancel` is also necessary - it may be required for tasks that use `IO.checkCanceled`
instead of `Core.checkInterrupted`.
-/
def asTask (t : CoreM α) : CoreM (BaseIO Unit × Task (CoreM α)) := do
  let cancelToken ← IO.CancelToken.new
  -- Use wrapAsync to properly handle name generators and heartbeats,
  -- but modify it to return both the result and state
  let wrappedAct ← Core.wrapAsync (fun () => do let a ← t; let s ← get; return (a, s)) (some cancelToken)
  let task ← (wrappedAct ()).asTask
  return (cancelToken.set, task.map (sync := true) fun result =>
    match result with
    | .ok (a, s) => do
        -- Set state to the task's state (not merging)
        set s
        return a
    | .error e => throw e)

/--
Given a monadic value in `CoreM`, creates a task that runs it in the current state,
returning a monadic value with the cached result (and subsequent state as it was after running).
-/
def asTask' (t : CoreM α) : CoreM (Task (CoreM α)) := (·.2) <$> asTask t

end Lean.Core.CoreM

namespace Lean.Meta.MetaM

/--
Given a monadic value in `MetaM`, creates a task that runs it in the current state,
returning
* a cancellation hook and
* a monadic value with the cached result (and subsequent state as it was after running).
-/
def asTask (t : MetaM α) : MetaM (BaseIO Unit × Task (MetaM α)) := do
  let (cancel, task) ← (t.run (← read) (← get)).asTask
  return (cancel, task.map (sync := true)
    fun c : CoreM (α × Meta.State) => do let (a, s) ← c; set s; pure a)

/--
Given a monadic value in `MetaM`, creates a task that runs it in the current state,
returning a monadic value with the cached result (and subsequent state as it was after running).
-/
def asTask' (t : MetaM α) : MetaM (Task (MetaM α)) := (·.2) <$> asTask t

end Lean.Meta.MetaM

namespace Lean.Elab.Term.TermElabM

/--
Given a monadic value in `TermElabM`, creates a task that runs it in the current state,
returning
* a cancellation hook and
* a monadic value with the cached result (and subsequent state as it was after running).
-/
def asTask (t : TermElabM α) : TermElabM (BaseIO Unit × Task (TermElabM α)) := do
  let (cancel, task) ← (t.run (← read) (← get)).asTask
  return (cancel, task.map (sync := true)
    fun c : MetaM (α × Term.State) => do let (a, s) ← c; set s; pure a)

/--
Given a monadic value in `TermElabM`, creates a task that runs it in the current state,
returning a monadic value with the cached result (and subsequent state as it was after running).
-/
def asTask' (t : TermElabM α) : TermElabM (Task (TermElabM α)) := (·.2) <$> asTask t

end Lean.Elab.Term.TermElabM

namespace Lean.Elab.Tactic.TacticM

/--
Given a monadic value in `TacticM`, creates a task that runs it in the current state,
returning
* a cancellation hook and
* a monadic value with the cached result (and subsequent state as it was after running).
-/
def asTask (t : TacticM α) : TacticM (BaseIO Unit × Task (TacticM α)) := do
  let (cancel, task) ← (t (← read) |>.run (← get)).asTask
  return (cancel, task.map (prio := .max)
    fun c : TermElabM (α × Tactic.State) => do let (a, s) ← c; set s; pure a)

/--
Given a monadic value in `TacticM`, creates a task that runs it in the current state,
returning a monadic value with the cached result (and subsequent state as it was after running).
-/
def asTask' (t : TacticM α) : TacticM (Task (TacticM α)) := (·.2) <$> asTask t

end Lean.Elab.Tactic.TacticM
