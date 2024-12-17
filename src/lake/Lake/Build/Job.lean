/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.Util.Task
import Lake.Build.Basic

open System

namespace Lake

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

@[inline] def JobAction.merge (a b : JobAction) : JobAction :=
  max a b

def JobAction.verb (failed : Bool) : JobAction → String
| .unknown => if failed then "Running" else "Ran"
| .replay => if failed then "Replaying" else "Replayed"
| .fetch => if failed then "Fetching" else "Fetched"
| .build => if failed then "Building" else "Built"

/-- Mutable state of a Lake job. -/
structure JobState where
  /-- The job's log. -/
  log : Log := {}
  /-- Tracks whether this job performed any significant build action. -/
  action : JobAction := .unknown
  deriving Inhabited

/--
Resets the job state after a checkpoint (e.g., registering the job).
Preserves state that downstream jobs want to depend on while resetting
job-local state that should not be inherited by downstream jobs.
-/
@[inline] def JobState.renew (_ : JobState) : JobState where
  log := {}
  action := .unknown

def JobState.merge (a b : JobState) : JobState where
  log := a.log ++ b.log
  action := a.action.merge b.action

@[inline] def JobState.modifyLog (f : Log → Log) (s : JobState) :=
  {s with log := f s.log}

/-- The result of a Lake job. -/
abbrev JobResult α := EResult Log.Pos JobState α

/-- Add log entries to the beginning of the job's log. -/
def JobResult.prependLog (log : Log) (self : JobResult α) : JobResult α :=
  match self with
  | .ok a s => .ok a <| s.modifyLog (log ++ ·)
  | .error e s => .error ⟨log.size + e.val⟩ <| s.modifyLog (log ++ ·)

/-- The `Task` of a Lake job. -/
abbrev JobTask α := BaseIOTask (JobResult α)

/--
The monad of asynchronous Lake jobs.

While this can be lifted into `FetchM`, job action should generally
be wrapped into an asynchronous job (e.g., via `Job.async`) instead of being
run directly in `FetchM`.
-/
abbrev JobM := BuildT <| EStateT Log.Pos JobState BaseIO

instance [Pure m] : MonadLift LakeM (BuildT m) where
  monadLift x := fun ctx => pure <| x.run ctx.toContext

instance : MonadStateOf Log JobM where
  get := (·.log) <$> get
  set log := modify fun s => {s with log}
  modifyGet f := modifyGet fun s => let (a, log) := f s.log; (a, {s with log})

instance : MonadStateOf JobState JobM := inferInstance

instance : MonadLog JobM := .ofMonadState
instance : MonadError JobM := ELog.monadError
instance : Alternative JobM := ELog.alternative
instance : MonadLift LogIO JobM := ⟨ELogT.takeAndRun⟩

/-- Record that this job is trying to perform some action. -/
@[inline] def updateAction (action : JobAction) : JobM PUnit :=
  modify fun s => {s with action := s.action.merge action}

/-- The monad used to spawn asynchronous Lake build jobs. Lifts into `FetchM`. -/
abbrev SpawnM := BuildT BaseIO

/-- The monad used to spawn asynchronous Lake build jobs. **Replaced by `SpawnM`.** -/
@[deprecated SpawnM (since := "2024-05-21")] abbrev SchedulerM := SpawnM

/-- A Lake job. -/
abbrev Job (α : Type u)  := JobCore (JobTask α)

structure BundledJobTask where
  {Result : Type u}
  task : JobTask Result
  deriving Inhabited

instance : CoeOut (JobTask α) BundledJobTask := ⟨.mk⟩

hydrate_opaque_type OpaqueJobTask BundledJobTask

abbrev OpaqueJob.Result (job : OpaqueJob) : Type :=
  job.task.get.Result

nonrec abbrev OpaqueJob.task (job : OpaqueJob) : JobTask job.Result :=
  job.task.get.task

abbrev OpaqueJob.ofJob (job : Job α) : OpaqueJob :=
  {job with task := job.task}

instance : CoeOut (Job α) OpaqueJob := ⟨.ofJob⟩

abbrev OpaqueJob.toJob (job : OpaqueJob) : Job job.Result :=
  {job with task := job.task}

instance : CoeDep OpaqueJob job (Job job.Result) := ⟨job.toJob⟩

namespace Job

@[inline] def ofTask (task : JobTask α) (caption := "") : Job α :=
  {task, caption}

@[inline] protected def error (log : Log := {}) (caption := "") : Job α :=
  {task := Task.pure (.error 0 {log}), caption}

@[inline] protected def pure (a : α) (log : Log := {}) (caption := "") : Job α :=
  {task := Task.pure (.ok a {log}), caption}

instance : Pure Job := ⟨Job.pure⟩
instance [Inhabited α] : Inhabited (Job α) := ⟨pure default⟩

@[inline] protected def nop (log : Log := {}) (caption := "") : Job Unit :=
  .pure () log caption

/-- Sets the job's caption. -/
@[inline] def setCaption (caption : String) (job : Job α) : Job α :=
  {job with caption}

/-- Sets the job's caption if the job's current caption is empty. -/
@[inline] def setCaption? (caption : String) (job : Job α) : Job α :=
  if job.caption.isEmpty then {job with caption} else job

@[inline] def mapResult
  (f : JobResult α → JobResult β) (self : Job α)
  (prio := Task.Priority.default) (sync := false)
: Job β :=
  {self with task := self.task.map f prio sync}

@[inline] def bindTask [Monad m]
  (f : JobTask α → m (JobTask β)) (self : Job α)
: m (Job β) :=
  return {self with task := ← f self.task}

@[inline] protected def map
  (f : α → β) (self : Job α)
  (prio := Task.Priority.default) (sync := false)
: Job β :=
  self.mapResult (·.map f) prio sync

instance : Functor Job where map := Job.map

/--
Resets the job's state after a checkpoint (e.g., registering the job).
Preserves information that downstream jobs want to depend on while resetting
job-local information that should not be inherited by downstream jobs.
-/
def renew (self : Job α) : Job α :=
  self.mapResult (sync := true) fun
  | .ok a s => .ok a s.renew
  | .error _ s => .error 0 s.renew

/-- Spawn a job that asynchronously performs `act`. -/
@[inline] protected def async
  (act : JobM α) (prio := Task.Priority.default)
: SpawnM (Job α) := fun ctx => .ofTask <$> do
  BaseIO.asTask (prio := prio) do (withLoggedIO act) ctx {}

/-- Wait a the job to complete and return the result. -/
@[inline] protected def wait (self : Job α) : BaseIO (JobResult α) := do
  IO.wait self.task

/--
Wait for a job to complete and return the produced value.
If an error occurred, return `none` and discarded any logs produced.
-/
@[inline] protected def wait? (self : Job α) : BaseIO (Option α) := do
  return (← self.wait).result?

/--
Wait for a job to complete and return the produced value.
Logs the job's log and throws if there was an error.
-/
@[inline] protected def await (self : Job α) : LogIO α := do
  match (← self.wait) with
  | .error n {log, ..} => log.replay; throw n
  | .ok a {log, ..} => log.replay; pure a

/--
`let c ← a.bindSync b` asynchronously performs the action `b`
after the job `a` completes.
-/
@[inline] protected def bindSync
  (self : Job α) (f : α → JobM β)
  (prio := Task.Priority.default) (sync := false)
: SpawnM (Job β) := fun ctx => self.bindTask fun task => do
  BaseIO.mapTask (t := task) (prio := prio) (sync := sync) fun
    | EResult.ok a s => (withLoggedIO (f a)) ctx s
    | EResult.error n s => return .error n s

/--
`let c ← a.bindAsync b` asynchronously performs the action `b`
after the job `a` completes and then merges into the job produced by `b`.
-/
@[inline] protected def bindAsync
  (self : Job α) (f : α → SpawnM (Job β))
  (prio := Task.Priority.default) (sync := false)
: SpawnM (Job β) := fun ctx => self.bindTask fun task => do
  BaseIO.bindTask task (prio := prio) (sync := sync) fun
    | .ok a sa => do
      let job ← f a ctx
      return job.task.map (prio := prio) (sync := true) fun
      | EResult.ok a sb => .ok a (sa.merge sb)
      | EResult.error n sb => .error ⟨sa.log.size + n.val⟩ (sa.merge sb)
    | .error n l => return Task.pure (.error n l)

/--
`a.zipWith f b` produces a new job `c` that applies `f` to the
results of `a` and `b`. The job `c` errors if either `a` or `b` error.
-/
@[inline] def zipWith
  (f : α → β → γ) (x : Job α) (y : Job β)
  (prio := Task.Priority.default) (sync := false)
: Job γ := Job.ofTask $
  x.task.bind (prio := prio) (sync := true) fun rx =>
  y.task.map (prio := prio) (sync := sync) fun ry =>
  match rx, ry with
  | .ok a sa, .ok b sb => .ok (f a b) (sa.merge sb)
  | rx, ry => .error 0 (rx.state.merge ry.state)

end Job

/-- A Lake build job. -/
abbrev BuildJob α := Job (α × BuildTrace)

namespace BuildJob

@[inline] def mk (job : Job (α × BuildTrace)) : BuildJob α :=
  job

@[inline] def ofJob (self : Job BuildTrace) : BuildJob Unit :=
  mk <| ((), ·) <$> self

@[inline] def toJob (self : BuildJob α) : Job (α × BuildTrace) :=
  self

@[inline] def nil : BuildJob Unit :=
  mk <| pure ((), nilTrace)

@[inline] protected def pure (a : α) : BuildJob α :=
  mk <| pure (a, nilTrace)

instance : Pure BuildJob := ⟨BuildJob.pure⟩

@[inline] protected def map (f : α → β) (self : BuildJob α) : BuildJob β :=
  mk <| (fun (a,t) => (f a,t)) <$> self.toJob

instance : Functor BuildJob where
  map := BuildJob.map

@[inline] def mapWithTrace (f : α → BuildTrace → β × BuildTrace) (self : BuildJob α) : BuildJob β :=
  mk <| (fun (a,t) => f a t) <$> self.toJob

@[inline] protected def bindSync
  (self : BuildJob α) (f : α → BuildTrace → JobM β)
  (prio : Task.Priority := .default) (sync := false)
: SpawnM (Job β) :=
  self.toJob.bindSync (prio := prio) (sync := sync) fun (a, t) => f a t

@[inline] protected def bindAsync
  (self : BuildJob α) (f : α → BuildTrace → SpawnM (Job β))
  (prio : Task.Priority := .default) (sync := false)
 : SpawnM (Job β)  :=
  self.toJob.bindAsync (prio := prio) (sync := sync) fun (a, t) => f a t

@[inline] protected def wait? (self : BuildJob α) : BaseIO (Option α) :=
  (·.map (·.1)) <$> self.toJob.wait?

def add (self : BuildJob α) (other : BuildJob β) : BuildJob α :=
  mk <| self.toJob.zipWith (fun a _ => a) other.toJob

def mix (self : BuildJob α) (other : BuildJob β) : BuildJob Unit :=
  mk <| self.toJob.zipWith (fun (_,t) (_,t') => ((), mixTrace t t')) other.toJob

def mixList (jobs : List (BuildJob α)) : Id (BuildJob Unit) := ofJob $
  jobs.foldr (·.toJob.zipWith (fun (_,t') t => mixTrace t t') ·) (pure nilTrace)

def mixArray (jobs : Array (BuildJob α)) : Id (BuildJob Unit) := ofJob $
  jobs.foldl (·.zipWith (fun t (_,t') => mixTrace t t') ·.toJob) (pure nilTrace)

def zipWith
  (f : α → β → γ) (self : BuildJob α) (other : BuildJob β)
: BuildJob γ :=
  mk <| self.toJob.zipWith (fun (a,t) (b,t') => (f a b, mixTrace t t')) other.toJob

def collectList (jobs : List (BuildJob α)) : Id (BuildJob (List α)) :=
  return jobs.foldr (zipWith List.cons) (pure [])

def collectArray (jobs : Array (BuildJob α)) : Id (BuildJob (Array α)) :=
  return jobs.foldl (zipWith Array.push) (pure (Array.mkEmpty jobs.size))
