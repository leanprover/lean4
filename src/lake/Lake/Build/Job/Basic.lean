/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lake.Util.Log
public import Lake.Util.Task
public import Lake.Util.Opaque
public import Lake.Build.Trace
public import Lake.Build.Data

/-! # Job Primitives

This module contains the basic definitions of a Lake `Job`. In particular,
it defines `OpaqueJob`, which is needed for `BuildContext`. More complex
utilities are defined in `Lake.Build.Job.Monad`, which depends on `BuildContext`.
-/

open System Lean

namespace Lake

/-! ## JobAction -/

/-- Information on what this job did. -/
public inductive JobAction
/-- No information about this job's action is available. -/
| unknown
/-- Tried to replay a cached build action (set by `buildFileUnlessUpToDate`) -/
| replay
/-- Tried to fetch a build from a store (can be set by `buildUnlessUpToDate?`) -/
| fetch
/-- Tried to perform a build action (set by `buildUnlessUpToDate?`) -/
| build
deriving Inhabited, Repr, DecidableEq, Ord

namespace JobAction

public instance : LT JobAction := ltOfOrd
public instance : LE JobAction := leOfOrd
public instance : Min JobAction := minOfLe
public instance : Max JobAction := maxOfLe

public def merge (a b : JobAction) : JobAction :=
  max a b

public def verb (failed : Bool) : JobAction → String
| .unknown => if failed then "Running" else "Ran"
| .replay => if failed then "Replaying" else "Replayed"
| .fetch => if failed then "Fetching" else "Fetched"
| .build => if failed then "Building" else "Built"

end JobAction

/-! ## JobState -/

/-- Mutable state of a Lake job. -/
public structure JobState where
  /-- The job's log. -/
  log : Log := {}
  /-- Tracks whether this job performed any significant build action. -/
  action : JobAction := .unknown
  /-- Whether this job failed due to a request to rebuild for `--no-build`. -/
  wantsRebuild : Bool := false
  /-- Current trace of a build job. -/
  trace : BuildTrace := .nil
  /-- How long the job spent building (in milliseconds). -/
  buildTime : Nat := 0
  deriving Inhabited

public def JobState.merge (a b : JobState) : JobState where
  log := a.log ++ b.log
  action := a.action.merge b.action
  wantsRebuild := a.wantsRebuild || b.wantsRebuild
  trace := mixTrace a.trace b.trace
  buildTime := a.buildTime + b.buildTime

@[inline] public def JobState.modifyLog (f : Log → Log) (s : JobState) : JobState :=
  {s with log := f s.log}

@[inline] public def JobState.logEntry (e : LogEntry) (s : JobState) :=
  s.modifyLog (·.push e)

/-! ## JobTask -/

/-- The result of a Lake job. -/
public abbrev JobResult α := EResult Log.Pos JobState α

/-- Add log entries to the beginning of the job's log. -/
public def JobResult.prependLog (log : Log) (self : JobResult α) : JobResult α :=
  match self with
  | .ok a s => .ok a <| s.modifyLog (log ++ ·)
  | .error e s => .error ⟨log.size + e.val⟩ <| s.modifyLog (log ++ ·)

/-- The `Task` of a Lake job. -/
public abbrev JobTask α := BaseIOTask (JobResult α)

/-! ## Job -/

/-- A Lake job. -/
public structure Job (α : Type u) where
  /-- The Lean `Task` object for the job. -/
  task : JobTask α
   /-- The kind of data this job produces. -/
  [kind : OptDataKind α]
  /--
  A caption for the job in Lake's build monitor.
  Will be formatted like `✔ [3/5] Ran <caption>`.
  -/
  caption : String
  /-- Whether this job failing should cause the build to fail. -/
  optional : Bool := false

public instance : Inhabited (Job α) := ⟨{task := default, caption := default, kind := .anonymous}⟩

namespace Job

set_option backward.whnf.reducibleClassField false in
public protected def cast (self : Job α) (h : ¬ self.kind.isAnonymous) : Job (DataType self.kind) :=
  let h := by
    match kind_eq:self.kind with
    | ⟨_, wf⟩ =>
      simp only
      simp only [OptDataKind.isAnonymous_iff_name_isAnonymous, kind_eq] at h
      rw [wf h]
  cast h self

@[inline] public def ofTask [OptDataKind α] (task : JobTask α) (caption := "") : Job α :=
  {task, caption}

@[inline] public protected def error [OptDataKind α] (log : Log := {}) (caption := "") : Job α :=
  .ofTask (Task.pure (.error 0 {log})) caption

@[inline] public protected def pure [kind : OptDataKind α] (a : α) (log : Log := {}) (caption := "") : Job α :=
  .ofTask (Task.pure (.ok a {log})) caption

public instance : Pure Job := ⟨Job.pure⟩

/-- **For internal use.** -/
@[inline] public def traceRoot (a : α) (caption := "<root>")  : Job α :=
  .ofTask <| .pure <| .ok a {trace := .nil caption}

@[inline] public def nop (log : Log := {}) (caption := "") : Job Unit :=
  .pure () log caption

@[inline] public def nil (traceCaption := "<nil>") : Job Unit :=
  .traceRoot () traceCaption

/--
Waits for the job and returns it trace.
Useful if the job is already known to be completed.
-/
@[inline] public def getTrace (job : Job α) : BuildTrace :=
  job.task.get.state.trace

/-- Sets the job's caption. -/
@[inline] public def setCaption (caption : String) (job : Job α) : Job α :=
  {job with caption}

/-- Sets the job's caption if the job's current caption is empty. -/
@[inline] public def setCaption? (caption : String) (job : Job α) : Job α :=
  if job.caption.isEmpty then {job with caption} else job

@[inline] public def mapResult
  [OptDataKind β] (f : JobResult α → JobResult β) (self : Job α)
  (prio := Task.Priority.default) (sync := false)
: Job β := {self with task := self.task.map f prio sync, kind := inferInstance}

@[inline] public def mapOk
  [OptDataKind β] (f : α → JobState → JobResult β) (self : Job α)
  (prio := Task.Priority.default) (sync := false)
: Job β :=
  self.mapResult (prio := prio) (sync := sync) fun
    | .ok a s => f a s
    | .error e s => .error e s

@[inline] public protected def map
  [OptDataKind β] (f : α → β) (self : Job α)
  (prio := Task.Priority.default) (sync := false)
: Job β := self.mapResult (·.map f) prio sync

public instance : Functor Job where map := Job.map

end Job

/-! ## OpaqueJob -/

/-- A Lake job task with an opaque value in `Type`. -/
public abbrev OpaqueJobTask := JobTask Opaque

@[inline] private unsafe def JobTask.toOpaqueImpl (self : JobTask α) : OpaqueJobTask :=
  unsafeCast self

/-- Forget the value of a job task. Implemented as a no-op cast. -/
@[implemented_by toOpaqueImpl]
public def JobTask.toOpaque (self : JobTask α) : OpaqueJobTask :=
  self.map (·.map Opaque.mk)

public instance : CoeOut (JobTask α) OpaqueJobTask := ⟨.toOpaque⟩

/-- A Lake job with an opaque value in `Type`. -/
public abbrev OpaqueJob := Job Opaque

/-- Forget the value of a job. Implemented as a no-op cast on the task. -/
public def Job.toOpaque (job : Job α) : OpaqueJob :=
  {job with task := job.task.toOpaque, kind := .anonymous}

public instance : CoeOut (Job α) OpaqueJob := ⟨.toOpaque⟩
