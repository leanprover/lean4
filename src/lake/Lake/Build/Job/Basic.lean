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

def JobState.merge (a b : JobState) : JobState where
  log := a.log ++ b.log
  action := a.action.merge b.action
  trace := mixTrace a.trace b.trace

@[inline] def JobState.modifyLog (f : Log → Log) (s : JobState) : JobState :=
  {s with log := f s.log}

@[inline] def JobState.logEntry (e : LogEntry) (s : JobState) :=
  s.modifyLog (·.push e)

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

namespace Job

@[inline] def ofTask (task : JobTask α) (caption := "") : Job α :=
  {task, caption}

@[inline] protected def error (log : Log := {}) (caption := "") : Job α :=
  {task := Task.pure (.error 0 {log}), caption}

@[inline] protected def pure (a : α) (log : Log := {}) (caption := "") : Job α :=
  {task := Task.pure (.ok a {log}), caption}

instance : Pure Job := ⟨Job.pure⟩

@[inline] protected def nop (log : Log := {}) (caption := "") : Job Unit :=
  .pure () log caption

@[inline] def nil : Job Unit :=
  .pure ()

/-- Sets the job's caption. -/
@[inline] def setCaption (caption : String) (job : Job α) : Job α :=
  {job with caption}

/-- Sets the job's caption if the job's current caption is empty. -/
@[inline] def setCaption? (caption : String) (job : Job α) : Job α :=
  if job.caption.isEmpty then {job with caption} else job

@[inline] def mapResult
  (f : JobResult α → JobResult β) (self : Job α)
  (prio := Task.Priority.default) (sync := false)
: Job β := {self with task := self.task.map f prio sync}

@[inline] def mapOk
  (f : α → JobState → JobResult β) (self : Job α)
  (prio := Task.Priority.default) (sync := false)
: Job β :=
  self.mapResult (prio := prio) (sync := sync) fun
    | .ok a s => f a s
    | .error e s => .error e s

@[inline] protected def map
  (f : α → β) (self : Job α)
  (prio := Task.Priority.default) (sync := false)
: Job β := self.mapResult (·.map f) prio sync

instance : Functor Job where map := Job.map

end Job

/-! ## OpaqueJob -/

/-- A Lake job with an opaque value in `Type`. -/
abbrev OpaqueJob := Job Opaque

@[inline] private unsafe def Job.toOpaqueImpl (job : Job α) : OpaqueJob :=
  unsafeCast job

/-- Forget the value of a job. Implemented as a no-op cast. -/
@[implemented_by toOpaqueImpl]
def Job.toOpaque (job : Job α) : OpaqueJob :=
  {job with task := job.task.map (·.map Opaque.mk)}

instance : CoeOut (Job α) OpaqueJob := ⟨.toOpaque⟩
