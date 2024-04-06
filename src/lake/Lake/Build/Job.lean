/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Build.Trace
import Lake.Build.Basic

open System

namespace Lake

namespace Job

@[inline] protected def pure (a : α) : Job α :=
  {task := Task.pure (.ok a {})}

instance : Pure Job := ⟨Job.pure⟩
instance [Inhabited α] : Inhabited (Job α) := ⟨pure default⟩

@[inline] protected def nop : Job Unit :=
  pure ()

@[inline] protected def error (l : Log) : Job α :=
  {task := Task.pure (.error 0 l)}

@[inline] def mapResult
  (f : JobResult α → JobResult β) (self : Job α)
  (prio := Task.Priority.default) (sync := false)
: Job β :=
  {task := self.task.map f prio sync}

@[inline] protected def map
  (f : α → β) (self : Job α)
  (prio := Task.Priority.default) (sync := false)
: Job β :=
  self.mapResult (·.map f) prio sync

instance : Functor Job where map := Job.map

@[inline] def clearLog (self : Job α) : Job α :=
  self.mapResult (sync := true) fun
  | .ok a _ => .ok a {}
  | .error .. => .error 0 {}

@[inline] def attempt (self : Job α) : Job Bool :=
  self.mapResult (sync := true) fun
  | .error n l => .ok false (l.shrink n)
  | .ok _ l => .ok true l

@[inline] def attempt? (self : Job α) : Job (Option α) :=
  self.mapResult (sync := true) fun
  | .error n l => .ok none (l.shrink n)
  | .ok a l => .ok (some a) l

/-- Spawn a job that asynchronously performs `act`. -/
@[inline] protected def async
  (act : JobM α) (prio := Task.Priority.default)
: SpawnM (Job α) := fun ctx => Job.mk <$> do
  BaseIO.asTask (act ctx {}) prio

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
  | .error n l => l.replay; throw n
  | .ok a l => l.replay; pure a

/--
`let c ← a.bindSync b` asynchronously performs the action `b`
after the job `a` completes.
-/
@[inline] protected def bindSync
  (self : Job α) (f : α → JobM β)
  (prio := Task.Priority.default) (sync := false)
: SpawnM (Job β) := fun ctx => Job.mk <$> do
  BaseIO.mapTask (t := self.task) (prio := prio) (sync := sync) fun r=>
    match r with
    | EResult.ok a l => f a ctx l
    | EResult.error n l => return .error n l

/--
`let c ← a.bindAsync b` asynchronously performs the action `b`
after the job `a` completes and then merges into the job produced by `b`.
-/
@[inline] protected def bindAsync
  (self : Job α) (f : α → SpawnM (Job β))
  (prio := Task.Priority.default) (sync := false)
: SpawnM (Job β) := fun ctx => Job.mk <$> do
  BaseIO.bindTask self.task (prio := prio) (sync := sync) fun
    | .ok a l => do
      let job ← f a ctx
      if l.isEmpty then return job.task else
      return job.task.map (prio := prio) (sync := true) fun
      | EResult.ok a l' => .ok a (l ++ l')
      | EResult.error n l' => .error (l.size + n) (l ++ l')
    | .error n l => return Task.pure (.error n l)

/--
`a.zipWith f b` produces a new job `c` that applies `f` to the
results of `a` and `b`. The job `c` errors if either `a` or `b` error.
-/
@[inline] def zipWith
  (f : α → β → γ) (x : Job α) (y : Job β)
  (prio := Task.Priority.default) (sync := false)
: BaseIO (Job γ) := Job.mk <$> do
  BaseIO.bindTask x.task (prio := prio) (sync := true) fun rx =>
  BaseIO.bindTask y.task (prio := prio) (sync := sync) fun ry =>
  match rx, ry with
  | .ok a la, .ok b lb => return Task.pure (EResult.ok (f a b) (la ++ lb))
  | rx, ry => return Task.pure (EResult.error 0 (rx.state ++ ry.state))

end Job

/-- Register the produced job for the CLI progress UI.  -/
@[inline] def withRegisterJob
  [Monad m] [MonadReaderOf BuildContext m] [MonadLiftT BaseIO m]
  (caption : String) (x : m (Job α))
: m (Job α) := do
  let job ← x
  let ctx ← read
  liftM (m := BaseIO) do
  ctx.buildJobs.modify (·.push (caption, discard job))
  return job.clearLog

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

@[inline] def attempt (self : BuildJob α) : BuildJob Bool :=
  {task := self.toJob.task.map fun
    | .error _ l => .ok (false, nilTrace) l
    | .ok (_, t) l => .ok (true, t) l}

@[inline] def attempt? (self : BuildJob α) : BuildJob (Option α) :=
  {task := self.toJob.task.map fun
    | .error _ l => .ok (none, nilTrace) l
    | .ok (a, t) l => .ok (some a, t) l}

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

def add (t1 : BuildJob α) (t2 : BuildJob β) : BaseIO (BuildJob α) :=
  mk <$> t1.toJob.zipWith (fun a _ => a) t2.toJob

def mix (t1 : BuildJob α) (t2 : BuildJob β) : BaseIO (BuildJob Unit) :=
  mk <$> t1.toJob.zipWith (fun (_,t) (_,t') => ((), mixTrace t t')) t2.toJob

def mixList (jobs : List (BuildJob α)) : BaseIO (BuildJob Unit) := ofJob <$> do
  jobs.foldrM (·.toJob.zipWith (fun (_,t') t => mixTrace t t') ·) (pure nilTrace)

def mixArray (jobs : Array (BuildJob α)) : BaseIO (BuildJob Unit) := ofJob <$> do
  jobs.foldlM (·.zipWith (fun t (_,t') => mixTrace t t') ·.toJob) (pure nilTrace)

protected def zipWith
  (f : α → β → γ) (t1 : BuildJob α) (t2 : BuildJob β)
: BaseIO (BuildJob γ) :=
  mk <$> t1.toJob.zipWith (fun (a,t) (b,t') => (f a b, mixTrace t t'))  t2.toJob

def collectList (jobs : List (BuildJob α)) : BaseIO (BuildJob (List α)) :=
  jobs.foldrM (BuildJob.zipWith List.cons) (pure [])

def collectArray (jobs : Array (BuildJob α)) : BaseIO (BuildJob (Array α)) :=
  jobs.foldlM (BuildJob.zipWith Array.push) (pure #[])
