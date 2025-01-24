/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.Util.Log
import Lake.Util.Task
import Lake.Util.Opaque
import Lake.Build.Trace

/-! # Job Primitives

This module contains the basic definitions of a Lake `Job`. In particular,
it defines `OpaqueJob`, which is needed for `BuildContext`. More complex
utilities are defined in `Lake.Build.Job.Monad`, which depends on `BuildContext`.
-/

open System

namespace Lake

/-! ## JobAction -/

/-- Information on what this job did. -/
inductive JobAction
/-- No information about this job's action is available. -/
| unknown
/-- Tried to replay a cached build action (set by `buildFileUnlessUpToDate`) -/
| replay
/-- Tried to fetch a build from a store (can be set by `buildUnlessUpToDate?`) -/
| fetch
/-- Tried to perform a build action (set by `buildUnlessUpToDate?`) -/
| build
deriving Inhabited, Repr, DecidableEq, Ord

instance : LT JobAction := ltOfOrd
instance : LE JobAction := leOfOrd
instance : Min JobAction := minOfLe
instance : Max JobAction := maxOfLe

def JobAction.merge (a b : JobAction) : JobAction :=
  max a b

def JobAction.verb (failed : Bool) : JobAction → String
| .unknown => if failed then "Running" else "Ran"
| .replay => if failed then "Replaying" else "Replayed"
| .fetch => if failed then "Fetching" else "Fetched"
| .build => if failed then "Building" else "Built"

/-! ## JobState -/

/-- Mutable state of a Lake job. -/
structure JobState where
  /-- The job's log. -/
  log : Log := {}
  /-- Tracks whether this job performed any significant build action. -/
  action : JobAction := .unknown
  /-- Current trace of a build job. -/
  trace : BuildTrace := .nil
  deriving Inhabited

/--
Resets the job state after a checkpoint (e.g., registering the job).
Preserves state that downstream jobs want to depend on while resetting
job-local state that should not be inherited by downstream jobs.
-/
@[inline] def JobState.renew (s : JobState) : JobState where
  trace := s.trace

def JobState.merge (a b : JobState) : JobState where
  log := a.log ++ b.log
  action := a.action.merge b.action
  trace := mixTrace a.trace b.trace

@[inline] def JobState.modifyLog (f : Log → Log) (s : JobState) : JobState :=
  {s with log := f s.log}

/-! ## JobTask -/

/-- The result of a Lake job. -/
abbrev JobResult α := EResult Log.Pos JobState α

/-- Add log entries to the beginning of the job's log. -/
def JobResult.prependLog (log : Log) (self : JobResult α) : JobResult α :=
  match self with
  | .ok a s => .ok a <| s.modifyLog (log ++ ·)
  | .error e s => .error ⟨log.size + e.val⟩ <| s.modifyLog (log ++ ·)

/-- The `Task` of a Lake job. -/
abbrev JobTask α := BaseIOTask (JobResult α)

/-! ## Job -/

/-- A Lake job. -/
structure Job (α : Type u)  where
  /-- The Lean `Task` object for the job. -/
  task : JobTask α
  /--
  A caption for the job in Lake's build monitor.
  Will be formatted like `✔ [3/5] Ran <caption>`.
  -/
  caption : String
  /-- Whether this job failing should cause the build to fail. -/
  optional : Bool := false
  deriving Inhabited

/-- A Lake job with an opaque value in `Type`. -/
abbrev OpaqueJob := Job Opaque

@[inline] private unsafe def Job.toOpaqueImpl (job : Job α) : OpaqueJob :=
  unsafeCast job

/-- Forget the value of a job. Implemented as a no-op cast. -/
@[implemented_by toOpaqueImpl]
def Job.toOpaque (job : Job α) : OpaqueJob :=
  {job with task := job.task.map (·.map Opaque.mk)}

instance : CoeOut (Job α) OpaqueJob := ⟨.toOpaque⟩
