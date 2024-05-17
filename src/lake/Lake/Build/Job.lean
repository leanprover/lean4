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

def add (t1 : BuildJob α) (t2 : BuildJob β) : BuildJob α :=
  mk <| t1.toJob.zipWith (fun a _ => a) t2.toJob

def mix (t1 : BuildJob α) (t2 : BuildJob β) : BuildJob Unit :=
  mk <| t1.toJob.zipWith (fun (_,t) (_,t') => ((), mixTrace t t')) t2.toJob

def mixList (jobs : List (BuildJob α)) : Id (BuildJob Unit) := ofJob $
  jobs.foldr (·.toJob.zipWith (fun (_,t') t => mixTrace t t') ·) (pure nilTrace)

def mixArray (jobs : Array (BuildJob α)) : Id (BuildJob Unit) := ofJob $
  jobs.foldl (·.zipWith (fun t (_,t') => mixTrace t t') ·.toJob) (pure nilTrace)

def zipWith
  (f : α → β → γ) (t1 : BuildJob α) (t2 : BuildJob β)
: BuildJob γ :=
  mk <| t1.toJob.zipWith (fun (a,t) (b,t') => (f a b, mixTrace t t')) t2.toJob

def collectList (jobs : List (BuildJob α)) : Id (BuildJob (List α)) :=
  return jobs.foldr (zipWith List.cons) (pure [])

def collectArray (jobs : Array (BuildJob α)) : Id (BuildJob (Array α)) :=
  return jobs.foldl (zipWith Array.push) (pure #[])
