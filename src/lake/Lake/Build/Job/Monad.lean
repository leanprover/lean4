/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lake.Build.Fetch

open System Lean

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
public abbrev JobM := FetchT <| EStateT Log.Pos JobState BaseIO

/-- Construct a `FetchM` monad from its full functional representation. -/
@[inline] public def JobM.ofFn
  (f : IndexBuildFn RecBuildM → Option Package → CallStack BuildKey →
    IO.Ref BuildStore → BuildContext → JobState → BaseIO (EResult Log.Pos JobState α))
: JobM α := .mk fun fetch => fun pkg? stack store ctx => .mk fun s =>
  f fetch pkg? stack store ctx s

/-- Convert a `JobM` monad to its full functional representation. -/
@[inline] public def JobM.toFn (self : JobM α) :
  IndexBuildFn RecBuildM → Option Package → CallStack BuildKey →
    IO.Ref BuildStore → BuildContext → JobState → BaseIO (EResult Log.Pos JobState α)
:= fun fetch pkg? stack store ctx s => self.run fetch pkg? stack store ctx |>.run s

public instance (priority := high) : MonadStateOf JobState JobM := inferInstance

public instance : MonadStateOf Log JobM where
  get := (·.log) <$> get
  set log := modify fun s => {s with log}
  modifyGet f := modifyGet fun s => let (a, log) := f s.log; (a, {s with log})

public instance : MonadLog JobM := .ofMonadState
public instance : MonadError JobM := ELog.monadError
public instance : Alternative JobM := ELog.alternative
public instance : MonadLift LogIO JobM := ⟨ELogT.takeAndRun⟩

/-- Record that this job is trying to perform some action. -/
@[inline] public def updateAction (action : JobAction) : JobM PUnit :=
  modify fun s => {s with action := s.action.merge action}

/-- Returns the current job's build trace. -/
@[inline] public def getTrace : JobM BuildTrace :=
  (·.trace) <$> get

/-- Sets the current job's build trace. -/
@[inline] public def setTrace (trace : BuildTrace) : JobM PUnit :=
  modify fun s => {s with trace := trace}

/-- Replace the job's build trace with a new empty trace. -/
@[inline] public def newTrace (caption := "<nil>") : JobM PUnit :=
  setTrace (.nil caption)

/-- Mutates the job's trace, applying `f` to it.-/
@[inline] public def modifyTrace (f : BuildTrace → BuildTrace) : JobM PUnit :=
  modify fun s => {s with trace := f s.trace}

/-- Set the caption of the job's build trace. -/
@[inline] public def setTraceCaption (caption : String) : JobM PUnit :=
  modifyTrace ({· with caption := caption})

/-- Returns the current job's build trace and removes it from the state. -/
@[inline] public def takeTrace : JobM BuildTrace :=
  modifyGet fun s => (s.trace, {s with trace := nilTrace})

/-- Sets the current job's trace and returns the previous one. -/
@[inline] public def swapTrace (trace : BuildTrace) : JobM BuildTrace :=
  modifyGet fun s => (s.trace, {s with trace := trace})

/-- Mix a trace into the current job's build trace. -/
@[inline] public def addTrace (trace : BuildTrace) : JobM PUnit :=
  modifyTrace (·.mix trace)

  /-- Runs `x` with a new trace and then mixes it into the original trace. -/
@[inline] public def addSubTrace (caption : String) (x : JobM α) : JobM α := do
  let oldTrace ← swapTrace (.nil caption)
  let a ← x
  modifyTrace (oldTrace.mix ·)
  return a

/-- The monad used to spawn asynchronous Lake build jobs. Lifts into `FetchM`. -/
public abbrev SpawnM := FetchT <| ReaderT BuildTrace <| BaseIO

/-- Construct a `SpawnM` monad from its full functional representation. -/
@[inline] public def SpawnM.ofFn
  (f : IndexBuildFn RecBuildM → Option Package → CallStack BuildKey →
    IO.Ref BuildStore → BuildContext → BuildTrace → BaseIO α)
: SpawnM α := .mk fun fetch => fun pkg? stack store ctx s =>
  f fetch pkg? stack store ctx s

/-- Convert a `SpawnM` monad to its full functional representation. -/
@[inline] public def SpawnM.toFn (self : SpawnM α) :
  IndexBuildFn RecBuildM → Option Package → CallStack BuildKey →
    IO.Ref BuildStore → BuildContext → BuildTrace → BaseIO α
:= fun fetch pkg? stack store ctx s => self.run fetch pkg? stack store ctx |>.run s

@[inline] public def JobM.runSpawnM (x : SpawnM α) : JobM α := .ofFn fun fn pkg? stack store ctx s =>
  return .ok (← x.toFn fn pkg? stack store ctx s.trace) s

public instance : MonadLift SpawnM JobM := ⟨JobM.runSpawnM⟩

/-- Ensures that `SpawnM` lifts into `JobM`. -/
example : MonadLiftT SpawnM JobM := inferInstance

/--
Run a `JobM` action in `FetchM`.

Generally, this should not be done, and instead a job action
should be run asynchronously in a Job (e.g., via `Job.async`).
-/
@[inline] public def FetchM.runJobM (x : JobM α) : FetchM α :=
  .ofFn fun fetch pkg? stack store ctx log => do
  match (← x.toFn fetch pkg? stack store ctx {log}) with
  | .ok a s => return .ok a s.log
  | .error e s => return .error e s.log

public instance : MonadLift JobM FetchM := ⟨FetchM.runJobM⟩

/-- Ensures that `JobM` lifts into `FetchM`. -/
example : MonadLiftT JobM FetchM := inferInstance

/-- Ensures that `SpawnM` lifts into `FetchM`. -/
example : MonadLiftT SpawnM FetchM := inferInstance

/-- Run a `FetchM` action in `JobM`. -/
@[inline] public def JobM.runFetchM (x : FetchM α) : JobM α := .ofFn fun fetch pkg? stack store ctx s => do
  match (← x.toFn fetch pkg? stack store ctx s.log) with
  | .ok a log => return .ok a {s with log}
  | .error e log => return .error e {s with log}

public instance : MonadLift FetchM JobM := ⟨JobM.runFetchM⟩

/-- Ensures that `FetchM` lifts into `JobM`. -/
example : MonadLiftT FetchM JobM := inferInstance

namespace Job

@[inline] public def bindTask
  [Monad m] [OptDataKind β]
  (f : JobTask α → m (JobTask β)) (self : Job α)
: m (Job β) := return {self with task := ← f self.task, kind := inferInstance}

/-- Returns a job that has synchronously performed `act`. -/
@[nospecialize] public protected def sync
  [OptDataKind α] (act : JobM α) (caption := "")
: SpawnM (Job α) := .ofFn fun fetch pkg? stack store ctx _ =>
  .ofTask (caption := caption) <$> Task.pure <$>
    (withLoggedIO act).toFn fetch pkg? stack store ctx {}

/-- Spawn a job that asynchronously performs `act`. -/
@[nospecialize] public protected def async
  [OptDataKind α] (act : JobM α) (prio := Task.Priority.default) (caption := "")
: SpawnM (Job α) := .ofFn fun fetch pkg? stack store ctx _ =>
  .ofTask (caption := caption) <$> BaseIO.asTask (prio := prio) do
    (withLoggedIO act).toFn fetch pkg? stack store ctx {}

/-- Wait for a job to complete and return the result. -/
@[inline] public protected def wait (self : Job α) : BaseIO (JobResult α) := do
  IO.wait self.task

/--
Wait for a job to complete and return the produced value.
If an error occurred, return `none` and discarded any logs produced.
-/
@[inline] public protected def wait? (self : Job α) : BaseIO (Option α) := do
  return (← self.wait).result?

/--
Wait for a job to complete and return the produced value.
Logs the job's log and throws if there was an error.
-/
public protected def await (self : Job α) : LogIO α := do
  match (← self.wait) with
  | .error n {log, ..} => log.replay; throw n
  | .ok a {log, ..} => log.replay; pure a

/-- Apply `f` asynchronously to the job's output. -/
@[nospecialize] public protected def mapM
  [kind : OptDataKind β] (self : Job α) (f : α → JobM β)
  (prio := Task.Priority.default) (sync := false)
: SpawnM (Job β) := .ofFn fun fetch pkg? stack store ctx trace => do
  self.bindTask fun task => do
  BaseIO.mapTask (t := task) (prio := prio) (sync := sync) fun
    | .ok a s =>
      let trace := mixTrace trace s.trace
      withLoggedIO (f a) |>.toFn fetch pkg? stack store ctx {s with trace}
    | .error n s => return .error n s

/--
Apply `f` asynchronously to the job's output
and asynchronously await the resulting job.
-/
@[nospecialize] public def bindM
  [kind : OptDataKind β] (self : Job α) (f : α → JobM (Job β))
  (prio := Task.Priority.default) (sync := false)
: SpawnM (Job β) := .ofFn fun fetch pkg? stack store ctx trace => do
  self.bindTask fun task => do
  BaseIO.bindTask task (prio := prio) (sync := sync) fun
    | .ok a sa => do
      let trace := mixTrace trace sa.trace
      match (← withLoggedIO (f a) |>.toFn fetch pkg? stack store ctx {sa with trace}) with
      | .ok job sa =>
        return job.task.map (prio := prio) (sync := true) fun
        | .ok b sb => .ok b {sa.merge sb with trace := sb.trace}
        | .error e sb => .error ⟨sa.log.size + e.val⟩ {sa.merge sb with trace := sb.trace}
      | .error e sa => return Task.pure (.error e sa)
    | .error e sa => return Task.pure (.error e sa)

/--
`a.zipWith f b` produces a new job `c` that applies `f` to the
results of `a` and `b`. The job `c` errors if either `a` or `b` error.
-/
@[inline] public def zipResultWith
  [OptDataKind γ] (f : JobResult α → JobResult β → JobResult γ) (self : Job α) (other : Job β)
  (prio := Task.Priority.default) (sync := false)
: Job γ := Job.ofTask $
  self.task.bind (prio := prio) (sync := true) fun rx =>
  other.task.map (prio := prio) (sync := sync) fun ry =>
  f rx ry

/--
`a.zipWith f b` produces a new job `c` that applies `f` to the
results of `a` and `b`. The job `c` errors if either `a` or `b` error.
-/
@[inline] public def zipWith
  [OptDataKind γ] (f : α → β → γ) (self : Job α) (other : Job β)
  (prio := Task.Priority.default) (sync := false)
: Job γ :=
  self.zipResultWith (other := other) (prio := prio) (sync := sync) fun
  | .ok a sa, .ok b sb => .ok (f a b) (sa.merge sb)
  | ra, rb => .error 0 (ra.state.merge rb.state)

/-- Merges this job with another, discarding its output and trace. -/
public def add (self : Job α) (other : Job β) : Job α :=
  have : OptDataKind α := self.kind
  self.zipResultWith (other := other) fun
  | .ok a sa, .ok _ sb => .ok a {sa.merge sb with trace := sa.trace}
  | ra, rb => .error 0 {ra.state.merge rb.state with trace := ra.state.trace}

/-- Merges this job with another, discarding both outputs. -/
public def mix (self : Job α) (other : Job β) : Job Unit :=
  self.zipWith (sync := true) (fun _ _ => ()) other

/-- Merge a `List` of jobs into one, discarding their outputs. -/
public def mixList (jobs : List (Job α)) (traceCaption := "<collection>")  : Job Unit :=
  jobs.foldr (·.mix ·) (traceRoot () traceCaption)

/-- Merge an `Array` of jobs into one, discarding their outputs. -/
public def mixArray (jobs : Array (Job α)) (traceCaption := "<collection>")  : Job Unit :=
  jobs.foldl (·.mix ·) (traceRoot () traceCaption)

/-- Merge a `List` of jobs into one, collecting their outputs into a `List`. -/
public def collectList (jobs : List (Job α)) (traceCaption := "<collection>") : Job (List α) :=
  jobs.foldr (zipWith (sync := true) List.cons) (traceRoot [] traceCaption)

/-- Merge an `Array` of jobs into one, collecting their outputs into an `Array`. -/
public def collectArray (jobs : Array (Job α)) (traceCaption := "<collection>") : Job (Array α) :=
  jobs.foldl (zipWith (sync := true) Array.push) (traceRoot (Array.mkEmpty jobs.size) traceCaption)

private instance : Nonempty ({α : Type u} → [Nonempty α] → α) := ⟨Classical.ofNonempty⟩

/-- Merge an `Vector` of jobs into one, collecting their outputs into an `Array`. -/
public def collectVector {α : Type u} [Nonempty α] (jobs : Vector (Job α) n) (traceCaption := "<collection>") : Job (Vector α n) :=
  let placeholder := unsafe have : Nonempty α := inferInstance; (unsafeCast () : α)
  n.fold (init := traceRoot (Vector.replicate n placeholder) traceCaption) fun i h job =>
    job.zipWith (sync := true) (Vector.set · i · h) jobs[i]

end Job
