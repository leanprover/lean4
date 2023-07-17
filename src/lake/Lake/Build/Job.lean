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

/-- A Lake job. -/
abbrev Job α := OptionIOTask α

/-- The monad of Lake jobs. -/
abbrev JobM := BuildM

/-- The monad of a finished Lake job. -/
abbrev ResultM := OptionIO

namespace Job

@[inline] def nil : Job Unit :=
 pure ()

@[inline] protected def async (act : JobM α) : SchedulerM (Job α) :=
  async act

@[inline] protected def await (self : Job α) : ResultM α :=
  await self

@[inline] protected def bindSync
(self : Job α) (f : α → JobM β) (prio := Task.Priority.default) : SchedulerM (Job β) :=
  bindSync prio self f

@[inline] protected def bindAsync
(self : Job α) (f : α → SchedulerM (Job β)) : SchedulerM (Job β)  :=
  bindAsync self f

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
(prio : Task.Priority := .default) : SchedulerM (Job β) :=
  self.toJob.bindSync (prio := prio) fun (a, t) => f a t

@[inline] protected def bindAsync
(self : BuildJob α) (f : α → BuildTrace → SchedulerM (Job β)) : SchedulerM (Job β)  :=
  self.toJob.bindAsync fun (a, t) => f a t

@[inline] protected def await (self : BuildJob α) : ResultM α :=
  (·.1) <$> await self.toJob

instance : Await BuildJob ResultM := ⟨BuildJob.await⟩

@[inline] def materialize (self : BuildJob α) : ResultM Unit :=
  discard <| await self.toJob

def mix (t1 : BuildJob α) (t2 : BuildJob β) : BaseIO (BuildJob Unit) :=
  mk <$> seqWithAsync (fun (_,t) (_,t') => ((), mixTrace t t')) t1.toJob t2.toJob

def mixList (jobs : List (BuildJob α)) : BaseIO (BuildJob Unit) := ofJob <$> do
  jobs.foldrM (init := pure nilTrace) fun j a =>
    seqWithAsync (fun (_,t') t => mixTrace t t') j.toJob a

def mixArray (jobs : Array (BuildJob α)) : BaseIO (BuildJob Unit) := ofJob <$> do
  jobs.foldlM (init := pure nilTrace) fun a j =>
    seqWithAsync (fun t (_,t') => mixTrace t t') a j.toJob

protected def seqWithAsync
(f : α → β → γ) (t1 : BuildJob α) (t2 : BuildJob β) : BaseIO (BuildJob γ) :=
  mk <$> seqWithAsync (fun (a,t) (b,t') => (f a b, mixTrace t t')) t1.toJob t2.toJob

instance : SeqWithAsync BaseIO BuildJob := ⟨BuildJob.seqWithAsync⟩

def collectList (jobs : List (BuildJob α)) : BaseIO (BuildJob (List α)) :=
  jobs.foldrM (seqWithAsync List.cons) (pure [])

def collectArray (jobs : Array (BuildJob α)) : BaseIO (BuildJob (Array α)) :=
  jobs.foldlM (seqWithAsync Array.push) (pure #[])
