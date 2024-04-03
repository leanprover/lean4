/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Util.Async
import Lake.Build.Trace
import Lake.Build.Context

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

@[inline] def mapResult (f : EResult Nat Log α → EResult Nat Log β) (self : Job α) : Job β :=
  {task := self.task.map f}

@[inline] protected def map (f : α → β) (self : Job α) : Job β :=
  self.mapResult (·.map f)

instance : Functor Job where map := Job.map

@[inline] def clearLog (self : Job α) : Job α :=
  self.mapResult fun
  | .ok a _ => .ok a {}
  | .error .. => .error 0 {}

@[inline] def attempt (self : Job α) : Job Bool :=
  self.mapResult fun
  | .error n l => .ok false (l.shrink n)
  | .ok _ l => .ok true l

@[inline] def attempt? (self : Job α) : Job (Option α) :=
  self.mapResult fun
  | .error n l => .ok none (l.shrink n)
  | .ok a l => .ok (some a) l

@[inline] protected def async
  (act : JobM α) (prio := Task.Priority.default)
: SchedulerM (Job α) := fun ctx => Job.mk <$> liftM do
  BaseIO.asTask (act ctx {}) prio

@[inline] protected def await? (self : Job α) : BaseIO (Option α) := do
  return (← IO.wait self.task).result?

@[inline] protected def await (self : Job α) : LogIO α := do
  match (← IO.wait self.task) with
  | .error n l => l.replay; throw n
  | .ok a l => l.replay; pure a

/--
`let c ← a.thenJobM b` asynchronously performs the action `b`
after the job `a` completes.
-/
@[inline] protected def thenJobM
  (self : Job α) (f : α → JobM β)
  (prio := Task.Priority.default) (sync := false)
: SchedulerM (Job β) := fun ctx => Job.mk <$> liftM do
  BaseIO.mapTask (t := self.task) (prio := prio) (sync := sync) fun r=>
    match (r : EResult Nat Log α) with
    | .ok a l => f a ctx l
    | .error n l => return .error n l

@[deprecated Job.thenJobM] protected abbrev bindSync := @Job.thenJobM

/--
`let c ← a.thenJob b` asynchronously performs the action `b`
after the job `a` completes and then merges into the job produced by `b`.
-/
@[inline] protected def thenJob
  (self : Job α) (f : α → SchedulerM (Job β))
  (prio := Task.Priority.default) (sync := false)
: SchedulerM (Job β) := fun ctx => Job.mk <$> liftM do
  BaseIO.bindTask self.task (prio := prio) (sync := sync) fun
    | .ok a l => do
      let (job, l) ← f a ctx l
      if l.isEmpty then return job.task else
      return job.task.map (prio := prio) (sync := true) fun
      | EResult.ok a l' => .ok a (l ++ l')
      | EResult.error n l' => .error (l.size + n) (l ++ l')
    | .error n l => return Task.pure (EResult.error n l)

@[deprecated Job.thenJob] protected abbrev bindAsync := @Job.thenJob

@[inline] def zipWith
  (f : α → β → γ) (x : Job α) (y : Job β)
  (prio := Task.Priority.default) (sync := false)
: BaseIO (Job γ) := Job.mk <$> liftM do
  BaseIO.bindTask x.task (prio := prio) (sync := true) fun rx =>
  BaseIO.bindTask y.task (prio := prio) (sync := sync) fun ry =>
  match rx, ry with
  | .ok a la, .ok b lb => return Task.pure (EResult.ok (f a b) (la ++ lb))
  | rx, ry => return Task.pure (EResult.error 0 (rx.state ++ ry.state))

end Job

/-- Register the produced build job for the CLI progress UI.  -/
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

@[inline] protected def thenJobM
(self : BuildJob α) (f : α → BuildTrace → JobM β)
(prio : Task.Priority := .default) : SchedulerM (Job β) :=
  self.toJob.bindSync (prio := prio) fun (a, t) => f a t

@[deprecated BuildJob.thenJobM] protected abbrev bindSync := @BuildJob.thenJobM

@[inline] protected def thenJob
(self : BuildJob α) (f : α → BuildTrace → SchedulerM (Job β)) : SchedulerM (Job β)  :=
  self.toJob.bindAsync fun (a, t) => f a t

@[deprecated BuildJob.thenJob] protected abbrev bindAsync := @BuildJob.thenJob

@[inline] protected def await? (self : BuildJob α) : BaseIO (Option α) :=
  (·.map (·.1)) <$> self.toJob.await?

def add (t1 : BuildJob α) (t2 : BuildJob β) : BaseIO (BuildJob α) :=
  mk <$> t1.toJob.zipWith (fun a _ => a) t2.toJob

def mix (t1 : BuildJob α) (t2 : BuildJob β) : BaseIO (BuildJob Unit) :=
  mk <$> t1.toJob.zipWith (fun (_,t) (_,t') => ((), mixTrace t t')) t2.toJob

def mixList (jobs : List (BuildJob α)) : BaseIO (BuildJob Unit) := ofJob <$> do
  jobs.foldrM (·.toJob.zipWith (fun (_,t') t => mixTrace t t') ·) (pure nilTrace)

def mixArray (jobs : Array (BuildJob α)) : BaseIO (BuildJob Unit) := ofJob <$> do
  jobs.foldlM (·.zipWith (fun t (_,t') => mixTrace t t') ·.toJob) (pure nilTrace)

protected def zipWith
(f : α → β → γ) (t1 : BuildJob α) (t2 : BuildJob β) : BaseIO (BuildJob γ) :=
  mk <$> t1.toJob.zipWith (fun (a,t) (b,t') => (f a b, mixTrace t t'))  t2.toJob

def collectList (jobs : List (BuildJob α)) : BaseIO (BuildJob (List α)) :=
  jobs.foldrM (BuildJob.zipWith List.cons) (pure [])

def collectArray (jobs : Array (BuildJob α)) : BaseIO (BuildJob (Array α)) :=
  jobs.foldlM (BuildJob.zipWith Array.push) (pure #[])
