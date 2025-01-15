/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.Build.Basic

open System

namespace Lake

def JobAction.verb (failed : Bool) : JobAction → String
| .unknown => if failed then "Running" else "Ran"
| .replay => if failed then "Replaying" else "Replayed"
| .fetch => if failed then "Fetching" else "Fetched"
| .build => if failed then "Building" else "Built"

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

@[inline] def JobState.modifyLog (f : Log → Log) (s : JobState) :=
  {s with log := f s.log}

@[inline] def JobState.logEntry (e : LogEntry) (s : JobState) :=
  s.modifyLog (·.push e)

/-- Add log entries to the beginning of the job's log. -/
def JobResult.prependLog (log : Log) (self : JobResult α) : JobResult α :=
  match self with
  | .ok a s => .ok a <| s.modifyLog (log ++ ·)
  | .error e s => .error ⟨log.size + e.val⟩ <| s.modifyLog (log ++ ·)

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
abbrev SpawnM := BuildT <| ReaderT BuildTrace <| BaseIO

@[inline] def JobM.runSpawnM (x : SpawnM α) : JobM α := fun ctx s =>
  return .ok (← x ctx s.trace) s

instance : MonadLift SpawnM JobM := ⟨JobM.runSpawnM⟩

/-- The monad used to spawn asynchronous Lake build jobs. **Replaced by `SpawnM`.** -/
@[deprecated SpawnM (since := "2024-05-21")] abbrev SchedulerM := SpawnM

@[inline] private unsafe def Job.toOpaqueImpl (job : Job α) : OpaqueJob :=
  unsafeCast job

/-- Forget the value of a job. Implemented as a no-op cast. -/
@[implemented_by toOpaqueImpl]
def Job.toOpaque (job : Job α) : OpaqueJob :=
  {job with task := job.task.map (·.map Opaque.mk)}

instance : CoeOut (Job α) OpaqueJob := ⟨.toOpaque⟩

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

@[inline] def bindTask [Monad m]
  (f : JobTask α → m (JobTask β)) (self : Job α)
: m (Job β) := return {self with task := ← f self.task}

@[inline] protected def map
  (f : α → β) (self : Job α)
  (prio := Task.Priority.default) (sync := false)
: Job β := self.mapResult (·.map f) prio sync

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

/-- Apply `f` asynchronously to the job's output. -/
protected def mapM
  (self : Job α) (f : α → JobM β)
  (prio := Task.Priority.default) (sync := false)
: SpawnM (Job β) :=
  fun ctx trace => do
  self.bindTask fun task => do
  BaseIO.mapTask (t := task) (prio := prio) (sync := sync) fun
    | .ok a s =>
      let trace := mixTrace trace s.trace
      withLoggedIO (f a) ctx {s with trace}
    | .error n s => return .error n s

@[deprecated Job.mapM (since := "2024-12-06")]
protected abbrev bindSync
  (self : Job α) (f : α → JobM β)
  (prio := Task.Priority.default) (sync := false)
: SpawnM (Job β) := self.mapM f prio sync

/--
Apply `f` asynchronously to the job's output
and asynchronously await the resulting job.
-/
def bindM
  (self : Job α) (f : α → JobM (Job β))
  (prio := Task.Priority.default) (sync := false)
: SpawnM (Job β) :=
  fun ctx trace => do
  self.bindTask fun task => do
  BaseIO.bindTask task (prio := prio) (sync := sync) fun
    | .ok a sa => do
      let trace := mixTrace trace sa.trace
      match (← withLoggedIO (f a) ctx {sa with trace}) with
      | .ok job sa =>
        return job.task.map (prio := prio) (sync := true) fun
        | .ok b sb => .ok b {sa.merge sb with trace := sb.trace}
        | .error e sb => .error ⟨sa.log.size + e.val⟩ {sa.merge sb with trace := sb.trace}
      | .error e sa => return Task.pure (.error e sa)
    | .error e sa => return Task.pure (.error e sa)

@[deprecated bindM (since := "2024-12-06")]
protected abbrev bindAsync
  (self : Job α) (f : α → SpawnM (Job β))
  (prio := Task.Priority.default) (sync := false)
: SpawnM (Job β) := self.bindM (fun a => f a) prio sync

/--
`a.zipWith f b` produces a new job `c` that applies `f` to the
results of `a` and `b`. The job `c` errors if either `a` or `b` error.
-/
@[inline] def zipResultWith
  (f : JobResult α → JobResult β → JobResult γ) (self : Job α) (other : Job β)
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
  (f : α → β → γ) (self : Job α) (other : Job β)
  (prio := Task.Priority.default) (sync := true)
: Job γ :=
  self.zipResultWith (other := other) (prio := prio) (sync := sync) fun
  | .ok a sa, .ok b sb => .ok (f a b) (sa.merge sb)
  | ra, rb => .error 0 (ra.state.merge rb.state)


/-- Merges this job with another, discarding its output and trace. -/
def add (self : Job α) (other : Job β) : Job α :=
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
  jobs.foldr (zipWith List.cons) (pure [])

/-- Merge an `Array` of jobs into one, collecting their outputs into an `Array`. -/
def collectArray (jobs : Array (Job α)) : Job (Array α) :=
  jobs.foldl (zipWith Array.push) (pure (Array.mkEmpty jobs.size))

end Job

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
protected abbrev pure (a : α) : BuildJob α :=
  Job.pure a

instance : Pure BuildJob := ⟨Job.pure⟩

@[deprecated Job.map (since := "2024-12-06")]
protected abbrev map (f : α → β) (self : BuildJob α) : BuildJob β :=
  self.toJob.map f

instance : Functor BuildJob where
  map := Job.map

@[inline, deprecated "Removed without replacement." (since := "2024-12-06")]
def mapWithTrace (f : α → BuildTrace → β × BuildTrace) (self : BuildJob α) : BuildJob β :=
  self.toJob.mapOk fun a s =>
    let (b, trace) := f a s.trace
    .ok b {s with trace}

@[inline, deprecated Job.mapM (since := "2024-12-06")]
protected def bindSync
  (self : BuildJob α) (f : α → BuildTrace → JobM (β × BuildTrace))
  (prio : Task.Priority := .default) (sync := false)
: SpawnM (Job β) :=
  self.toJob.mapM (prio := prio) (sync := sync) fun a => do
    let (b, trace) ← f a (← getTrace)
    setTrace trace
    return b

@[inline, deprecated Job.bindM (since := "2024-12-06")]
protected def bindAsync
  (self : BuildJob α) (f : α → BuildTrace → SpawnM (Job β))
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
  (f : α → β → γ) (self : BuildJob α) (other : BuildJob β)
: BuildJob γ :=
  self.toJob.zipWith f other.toJob

@[deprecated Job.collectList (since := "2024-12-06")]
abbrev collectList (jobs : List (BuildJob α)) : Id (BuildJob (List α)) :=
  return Job.collectList jobs

@[deprecated Job.collectArray (since := "2024-12-06")]
abbrev collectArray (jobs : Array (BuildJob α)) : Id (BuildJob (Array α)) :=
  return Job.collectArray jobs

attribute [deprecated Job (since := "2024-12-06")] BuildJob
