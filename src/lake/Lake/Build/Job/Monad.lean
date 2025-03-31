/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.Build.Fetch

open System

/-! # Job Monad

This module contains additional definitions for Lake `Job`.
In particular, it defines `JobM`, which uses `BuildContext`, which contains
`OpaqueJob`s, hence the module split.
-/

namespace Lake

/--
The monad of asynchronous Lake jobs.

While this can be lifted into `FetchM`, job action should generally
be wrapped into an asynchronous job (e.g., via `Job.async`) instead of being
run directly in `FetchM`.
-/
abbrev JobM := FetchT <| EStateT Log.Pos JobState BaseIO

instance (priority := high) : MonadStateOf JobState JobM := inferInstance

instance : MonadStateOf Log JobM where
  get := (·.log) <$> get
  set log := modify fun s => {s with log}
  modifyGet f := modifyGet fun s => let (a, log) := f s.log; (a, {s with log})

instance : MonadLog JobM := .ofMonadState
instance : MonadError JobM := ELog.monadError
instance : Alternative JobM := ELog.alternative
instance : MonadLift LogIO JobM := ⟨ELogT.takeAndRun⟩

/-- Record that this job is trying to perform some action. -/
@[inline] def updateAction (action : JobAction) : JobM PUnit :=
  modify fun s => {s with action := s.action.merge action}

/-- Returns the current job's build trace. -/
@[inline] def getTrace : JobM BuildTrace :=
  (·.trace) <$> get

/-- Sets the current job's build trace. -/
@[inline] def setTrace (trace : BuildTrace) : JobM PUnit :=
  modify fun s => {s with trace := trace}

/-- Mix a trace into the current job's build trace. -/
@[inline] def addTrace (trace : BuildTrace) : JobM PUnit :=
  modify fun s => {s with trace := s.trace.mix trace}

/-- Returns the current job's build trace and removes it from the state. -/
@[inline] def takeTrace : JobM BuildTrace :=
  modifyGet fun s => (s.trace, {s with trace := nilTrace})

/-- The monad used to spawn asynchronous Lake build jobs. Lifts into `FetchM`. -/
abbrev SpawnM := FetchT <| ReaderT BuildTrace <| BaseIO

@[inline] def JobM.runSpawnM (x : SpawnM α) : JobM α := fun fn stack store ctx s =>
  return .ok (← x fn stack store ctx s.trace) s

instance : MonadLift SpawnM JobM := ⟨JobM.runSpawnM⟩

/--
Run a `JobM` action in `FetchM`.

Generally, this should not be done, and instead a job action
should be run asynchronously in a Job (e.g., via `Job.async`).
-/
@[inline] def FetchM.runJobM (x : JobM α) : FetchM α := fun fetch stack store ctx log => do
  match (← x fetch stack store ctx {log}) with
  | .ok a s => return .ok a s.log
  | .error e s => return .error e s.log

instance : MonadLift JobM FetchM := ⟨FetchM.runJobM⟩

/-- Ensures that `JobM` lifts into `FetchM`. -/
example : MonadLiftT JobM FetchM := inferInstance

/-- Ensures that `SpawnM` lifts into `FetchM`. -/
example : MonadLiftT SpawnM FetchM := inferInstance

/-- Run a `FetchM` action in `JobM`. -/
@[inline] def JobM.runFetchM (x : FetchM α) : JobM α := fun fetch stack store ctx s => do
  match (← x fetch stack store ctx s.log) with
  | .ok a log => return .ok a {s with log}
  | .error e log => return .error e {s with log}

instance : MonadLift FetchM JobM := ⟨JobM.runFetchM⟩

/-- Ensures that `FetchM` lifts into `JobM`. -/
example : MonadLiftT FetchM JobM := inferInstance

/-- Ensures that `FetchM` lifts into `SpawnM`. -/
example : MonadLiftT SpawnM FetchM := inferInstance

namespace Job

@[inline] def bindTask
  [Monad m] [OptDataKind β]
  (f : JobTask α → m (JobTask β)) (self : Job α)
: m (Job β) := return {self with task := ← f self.task, kind := inferInstance}

/-- Spawn a job that asynchronously performs `act`. -/
@[inline] protected def async
  [OptDataKind α] (act : JobM α) (prio := Task.Priority.default) (caption := "")
: SpawnM (Job α) := fun fetch stack store ctx => .ofTask (caption := caption) <$> do
  BaseIO.asTask (prio := prio) do (withLoggedIO act) fetch stack store ctx {}

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

/-- Apply `f` asynchronously to the job's output. -/
protected def mapM
  [kind : OptDataKind β] (self : Job α) (f : α → JobM β)
  (prio := Task.Priority.default) (sync := false)
: SpawnM (Job β) :=
  fun fetch stack store ctx trace => do
  self.bindTask fun task => do
  BaseIO.mapTask (t := task) (prio := prio) (sync := sync) fun
    | .ok a s =>
      let trace := mixTrace trace s.trace
      withLoggedIO (f a) fetch stack store ctx {s with trace}
    | .error n s => return .error n s

@[deprecated Job.mapM (since := "2024-12-06")]
protected abbrev bindSync
  [OptDataKind β] (self : Job α) (f : α → JobM β)
  (prio := Task.Priority.default) (sync := false)
: SpawnM (Job β) := self.mapM f prio sync

/--
Apply `f` asynchronously to the job's output
and asynchronously await the resulting job.
-/
def bindM
  [kind : OptDataKind β] (self : Job α) (f : α → JobM (Job β))
  (prio := Task.Priority.default) (sync := false)
: SpawnM (Job β) :=
  fun fetch stack store ctx trace => do
  self.bindTask fun task => do
  BaseIO.bindTask task (prio := prio) (sync := sync) fun
    | .ok a sa => do
      let trace := mixTrace trace sa.trace
      match (← withLoggedIO (f a) fetch stack store ctx {sa with trace}) with
      | .ok job sa =>
        return job.task.map (prio := prio) (sync := true) fun
        | .ok b sb => .ok b {sa.merge sb with trace := sb.trace}
        | .error e sb => .error ⟨sa.log.size + e.val⟩ {sa.merge sb with trace := sb.trace}
      | .error e sa => return Task.pure (.error e sa)
    | .error e sa => return Task.pure (.error e sa)

@[deprecated bindM (since := "2024-12-06")]
protected abbrev bindAsync
  [OptDataKind β] (self : Job α) (f : α → SpawnM (Job β))
  (prio := Task.Priority.default) (sync := false)
: SpawnM (Job β) := self.bindM (fun a => f a) prio sync

/--
`a.zipWith f b` produces a new job `c` that applies `f` to the
results of `a` and `b`. The job `c` errors if either `a` or `b` error.
-/
@[inline] def zipResultWith
  [OptDataKind γ] (f : JobResult α → JobResult β → JobResult γ) (self : Job α) (other : Job β)
  (prio := Task.Priority.default) (sync := true)
: Job γ := Job.ofTask $
  self.task.bind (prio := prio) (sync := true) fun rx =>
  other.task.map (prio := prio) (sync := sync) fun ry =>
  f rx ry

/--
`a.zipWith f b` produces a new job `c` that applies `f` to the
results of `a` and `b`. The job `c` errors if either `a` or `b` error.
-/
@[inline] def zipWith
  [OptDataKind γ] (f : α → β → γ) (self : Job α) (other : Job β)
  (prio := Task.Priority.default) (sync := true)
: Job γ :=
  self.zipResultWith (other := other) (prio := prio) (sync := sync) fun
  | .ok a sa, .ok b sb => .ok (f a b) (sa.merge sb)
  | ra, rb => .error 0 (ra.state.merge rb.state)

/-- Merges this job with another, discarding its output and trace. -/
def add (self : Job α) (other : Job β) : Job α :=
  have : OptDataKind α := self.kind
  self.zipResultWith (other := other) fun
  | .ok a sa, .ok _ sb => .ok a {sa.merge sb with trace := sa.trace}
  | ra, rb => .error 0 {ra.state.merge rb.state with trace := ra.state.trace}

/-- Merges this job with another, discarding both outputs. -/
def mix (self : Job α) (other : Job β) : Job Unit :=
  self.zipWith (fun _ _ => ()) other

/-- Merge a `List` of jobs into one, discarding their outputs. -/
def mixList (jobs : List (Job α)) : Job Unit :=
  jobs.foldr (·.mix ·) nil

/-- Merge an `Array` of jobs into one, discarding their outputs. -/
def mixArray (jobs : Array (Job α)) : Job Unit :=
  jobs.foldl (·.mix ·) nil

/-- Merge a `List` of jobs into one, collecting their outputs into a `List`. -/
def collectList (jobs : List (Job α)) : Job (List α) :=
  jobs.foldr (zipWith List.cons) (.pure [])

/-- Merge an `Array` of jobs into one, collecting their outputs into an `Array`. -/
def collectArray (jobs : Array (Job α)) : Job (Array α) :=
  jobs.foldl (zipWith Array.push) (.pure (Array.mkEmpty jobs.size))

end Job

/-! ## BuildJob (deprecated) -/

/-- A Lake build job. -/
abbrev BuildJob α := Job α

namespace BuildJob

@[inline, deprecated "Obsolete." (since := "2024-12-06")]
def mk (job : Job (α × BuildTrace)) : BuildJob α :=
  job.mapOk fun (a, trace) s => .ok a {s with trace}

@[inline, deprecated "Obsolete." (since := "2024-12-06")]
def ofJob (job : Job BuildTrace) : BuildJob Unit :=
  job.mapOk fun trace s => .ok () {s with trace}

abbrev toJob (self : BuildJob α) : Job α :=
  self

@[deprecated Job.nil (since := "2024-12-06")]
abbrev nil : BuildJob Unit :=
  Job.pure ()

@[deprecated Job.map (since := "2024-12-06")]
protected abbrev pure [OptDataKind α] (a : α) : BuildJob α :=
  Job.pure a

instance : Pure BuildJob := ⟨Job.pure⟩

@[deprecated Job.map (since := "2024-12-06")]
protected abbrev map [OptDataKind β] (f : α → β) (self : BuildJob α) : BuildJob β :=
  self.toJob.map f

instance : Functor BuildJob where
  map := Job.map

@[inline, deprecated "Removed without replacement." (since := "2024-12-06")]
def mapWithTrace [OptDataKind β] (f : α → BuildTrace → β × BuildTrace) (self : BuildJob α) : BuildJob β :=
  self.toJob.mapOk fun a s =>
    let (b, trace) := f a s.trace
    .ok b {s with trace}

@[inline, deprecated Job.mapM (since := "2024-12-06")]
protected def bindSync
  [OptDataKind β] (self : BuildJob α) (f : α → BuildTrace → JobM (β × BuildTrace))
  (prio : Task.Priority := .default) (sync := false)
: SpawnM (Job β) :=
  self.toJob.mapM (prio := prio) (sync := sync) fun a => do
    let (b, trace) ← f a (← getTrace)
    setTrace trace
    return b

@[inline, deprecated Job.bindM (since := "2024-12-06")]
protected def bindAsync
  [OptDataKind β] (self : BuildJob α) (f : α → BuildTrace → SpawnM (Job β))
  (prio : Task.Priority := .default) (sync := false)
 : SpawnM (Job β)  :=
  self.toJob.bindM (prio := prio) (sync := sync) fun a => do
    f a (← getTrace)

@[deprecated Job.wait? (since := "2024-12-06")]
protected abbrev wait? (self : BuildJob α) : BaseIO (Option α) :=
  self.toJob.wait?

@[deprecated Job.add (since := "2024-12-06")]
abbrev add (self : BuildJob α) (other : BuildJob β) : BuildJob α :=
  self.toJob.add other.toJob

@[deprecated Job.mix (since := "2024-12-06")]
abbrev mix (self : BuildJob α) (other : BuildJob β) : BuildJob Unit :=
  self.toJob.mix other.toJob

@[deprecated Job.mixList (since := "2024-12-06")]
abbrev mixList (jobs : List (BuildJob α)) : Id (BuildJob Unit) :=
  return Job.mixList jobs

@[deprecated Job.mixArray (since := "2024-12-06")]
abbrev mixArray (jobs : Array (BuildJob α)) : Id (BuildJob Unit) :=
  return Job.mixArray jobs

@[deprecated Job.zipWith (since := "2024-12-06")]
abbrev zipWith
  [OptDataKind γ] (f : α → β → γ) (self : BuildJob α) (other : BuildJob β)
: BuildJob γ :=
  self.toJob.zipWith f other.toJob

@[deprecated Job.collectList (since := "2024-12-06")]
abbrev collectList (jobs : List (BuildJob α)) : Id (BuildJob (List α)) :=
  return Job.collectList jobs

@[deprecated Job.collectArray (since := "2024-12-06")]
abbrev collectArray (jobs : Array (BuildJob α)) : Id (BuildJob (Array α)) :=
  return Job.collectArray jobs

attribute [deprecated Job (since := "2024-12-06")] BuildJob
