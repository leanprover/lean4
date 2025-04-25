/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.Build.Fetch

/-! # Job Registration -/

namespace Lake

/--
Resets the job state after a checkpoint (e.g., registering the job).
Preserves state that downstream jobs want to depend on while resetting
job-local state that should not be inherited by downstream jobs.
-/
@[inline] def JobState.renew (s : JobState) : JobState where
  trace := s.trace.withoutInputs

/--
Resets the job's state after a checkpoint (e.g., registering the job).
Preserves information that downstream jobs want to depend on while resetting
job-local information that should not be inherited by downstream jobs.
-/
def Job.renew (self : Job α) : Job α :=
  have : OptDataKind α := self.kind
  self.mapResult (sync := true) fun
  | .ok a s => .ok a s.renew
  | .error _ s => .error 0 s.renew

/--
Registers the job for the top-level build monitor,
(e.g., the Lake CLI progress UI), assigning it `caption`.
-/
@[inline] def registerJob
  [Monad m] [MonadLiftT (ST IO.RealWorld) m] [MonadBuild m]
  (caption : String) (job : Job α) (optional := false)
: m (Job α) := do
  let job : Job α := {job with caption, optional}
  (← getBuildContext).registeredJobs.modify (·.push job)
  return job.renew

/-- Wraps stray I/O, logs, and errors in `x` into the produced job.  -/
def ensureJob
  [OptDataKind α] (x : FetchM (Job α))
: FetchM (Job α) := fun fetch stack store ctx log => do
  let iniPos := log.endPos
  match (← (withLoggedIO x) fetch stack store ctx log) with
  | .ok job log =>
    if iniPos < log.endPos then
      let (log, jobLog) := log.split iniPos
      let job := job.mapResult (sync := true) (·.prependLog jobLog)
      return .ok job log
    else
      return .ok job log
  | .error _ log =>
    let (log, jobLog) := log.split iniPos
    return .ok (.error jobLog) log

/--
Registers the produced job for the top-level build monitor
(e.g., the Lake CLI progress UI), assigning it `caption`.

Stray I/O, logs, and errors produced by `x` will be wrapped into the job.
-/
@[inline] def withRegisterJob
  [OptDataKind α] (caption : String) (x : FetchM (Job α)) (optional := false)
: FetchM (Job α) := do
  let job ← ensureJob x
  registerJob caption job optional

/--
Registers the produced job for the top-level build monitor
if it is not already (i.e., it has an empty caption).
-/
@[inline] def maybeRegisterJob
  (caption : String) (job : Job α)
: FetchM (Job α) := do
  if job.caption.isEmpty then
    registerJob caption job
  else
    return job
