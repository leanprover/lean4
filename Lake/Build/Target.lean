/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Util.Task
import Lake.Build.Trace

open System
namespace Lake

--------------------------------------------------------------------------------
-- # Active Targets
--------------------------------------------------------------------------------

structure ActiveTarget.{u,v,w} (i : Type u) (n : Type v → Type w) (t : Type v) where
  info : i
  task : n t

instance [Inhabited i] [Inhabited t] [Pure n] : Inhabited (ActiveTarget i n t) :=
  ⟨Inhabited.default, pure Inhabited.default⟩

namespace ActiveTarget

def withInfo (info : i') (self : ActiveTarget i n t) : ActiveTarget i' n t :=
  {self with info}

def withoutInfo (self : ActiveTarget i n t) : ActiveTarget PUnit n t :=
  self.withInfo ()

def withTask (task : n' t') (self : ActiveTarget i n t) : ActiveTarget i n' t' :=
  {self with task}

def opaque (task : n t) : ActiveTarget PUnit n t :=
  ⟨(), task⟩

protected def pure [Pure n] (info : i) (trace : t) : ActiveTarget i n t :=
  ⟨info, pure trace⟩

def nil [NilTrace t] [Pure n] : ActiveTarget PUnit n t :=
  mk () <| pure nilTrace

protected def mapAsync [Bind m] [MapAsync m n] (self : ActiveTarget i n α) (f : i → α → m β) : m (n β) :=
   mapAsync (f self.info) self.task

protected def mapOpaqueAsync [Bind m] [MapAsync m n] (self : ActiveTarget i n α) (f : α → m β) : m (n β) :=
   mapAsync f self.task

protected def bindAsync [BindAsync m n] (self : ActiveTarget i n α) (f : i → α → m (n β)) : m (n β) :=
  bindAsync self.task (f self.info)

protected def bindOpaqueAsync [BindAsync m n] (self : ActiveTarget i n α) (f : α → m (n β)) : m (n β) :=
  bindAsync self.task f

def materializeAsync [Pure m] (self : ActiveTarget i n t) : m (n t) :=
  pure self.task

def materialize [Await n m] (self : ActiveTarget i n t) : m t :=
  await self.task

def mixOpaqueAsync
[MixTrace t] [Monad m] [Pure n] [BindAsync m n]
(t1 : ActiveTarget α n t) (t2 : ActiveTarget β n t) : m (ActiveTarget PUnit n t) := do
  ActiveTarget.opaque <| ←
    t1.bindOpaqueAsync fun tr1 =>
    t2.bindOpaqueAsync fun tr2 =>
    pure <| pure <| mixTrace tr1 tr2

section
variable [NilTrace t] [MixTrace t] [Monad m]

def materializeList  [Await n m] (targets : List (ActiveTarget i n t)) : m t := do
  targets.foldlM (fun tr t => return mixTrace tr <| ← await t.task) nilTrace

def materializeArray [Await n m] (targets : Array (ActiveTarget i n t)) :  m t := do
  targets.foldlM (fun tr t => return mixTrace tr <| ← await t.task) nilTrace

variable [BindAsync m n] [Pure n]

def collectList (targets : List (ActiveTarget i n t)) : m (ActiveTarget (List i) n t) := do
  mk (targets.map (·.info)) <| ← foldlListAsync mixTraceM nilTrace <| targets.map (·.task)

def collectArray (targets : Array (ActiveTarget i n t)) : m (ActiveTarget (Array i) n t) := do
  mk (targets.map (·.info)) <| ← foldlArrayAsync mixTraceM nilTrace <| targets.map (·.task)

def collectOpaqueList (targets : List (ActiveTarget i n t)) : m (ActiveTarget PUnit n t) := do
  opaque <| ← foldlListAsync mixTraceM nilTrace <| targets.map (·.task)

def collectOpaqueArray (targets : Array (ActiveTarget i n t)) : m (ActiveTarget PUnit n t) := do
  opaque <| ← foldlArrayAsync mixTraceM nilTrace <| targets.map (·.task)

end
end ActiveTarget

--------------------------------------------------------------------------------
-- # Inactive Target
--------------------------------------------------------------------------------

structure Target.{u,v,v',w} (i : Type u) (m : Type v → Type w) (n : Type v' → Type v) (t : Type v') where
  info : i
  task : m (n t)

instance [Inhabited i] [Inhabited t] [Pure m] [Pure n] : Inhabited (Target i m n t) :=
  ⟨Inhabited.default, pure (pure Inhabited.default)⟩

namespace Target

def withInfo (info : i') (self : Target i m n t) : Target i' m n t :=
  {self with info}

def withoutInfo (self : Target i m n t) : Target PUnit m n t :=
  self.withInfo ()

def withTask (task : m' (n' t')) (self : Target i m n t) : Target i m' n' t' :=
  {self with task}

def opaque (task : m (n t)) : Target PUnit m n t :=
  mk () task

def active [Pure m] (target : ActiveTarget i n t) : Target i m n t :=
  mk target.info <| pure target.task

protected def pure [Pure m] [Pure n] (info : i) (trace : t) : Target i m n t :=
  mk info <| pure <| pure trace

def nil [NilTrace t] [Pure m] [Pure n] : Target PUnit m n t :=
  mk () <| pure <| pure nilTrace

def computeSync [ComputeTrace i m' t] [MonadLiftT m' m] [Async m n] [Functor m] [Pure n] (info : i) : Target i m n t :=
  mk info <| pure <$> computeTrace info

def computeAsync [ComputeTrace i m' t] [MonadLiftT m' m]  [Async m n] (info : i) : Target i m n t :=
  mk info <| async <| computeTrace info

def run [Monad m] (self : Target i m n t ) : m (ActiveTarget i n t) :=
  Functor.map (fun t => ActiveTarget.mk self.info t) self.task

protected def mapAsync [Bind m] [MapAsync m n] (self : Target i m n α) (f : i → α → m β) : m (n β) :=
  bind self.task fun tk => mapAsync (f self.info) tk

protected def mapOpaqueAsync [Bind m] [MapAsync m n] (self : Target i m n α) (f : α → m β) : m (n β) :=
  bind self.task fun tk => mapAsync f tk

protected def bindAsync [Bind m] [BindAsync m n] (self : Target i m n α) (f : i → α → m (n β)) : m (n β) :=
  bind self.task fun tk => bindAsync tk (f self.info)

protected def bindOpaqueAsync [Bind m] [BindAsync m n] (self : Target i m n α) (f : α → m (n β)) : m (n β) :=
  bind self.task fun tk => bindAsync tk f

def materializeAsync (self : Target i m n t) : m (n t) :=
  self.task

def materialize [Await n m] [Bind m] (self : Target i m n t) : m t := do
  self.task >>= await

def build  [Await n m] [Functor m] [Bind m] (self : Target i m n t) : m i := do
  Functor.mapConst self.info self.materialize

def mixOpaqueAsync
[MixTrace t] [Monad m] [Pure n] [BindAsync m n]
(t1 :  Target α m n t) (t2 :  Target β m n t) : Target PUnit m n t :=
  Target.opaque do
    let tk1 ← t1.materializeAsync
    let tk2 ← t2.materializeAsync
    bindAsync tk1 fun tr1 =>
    bindAsync tk2 fun tr2 =>
    pure <| pure <| mixTrace tr1 tr2

section
variable [NilTrace t] [MixTrace t] [Monad m]

def materializeList [Await n m] (targets : List (Target i m n t)) : m t := do
  let tasks ← targets.mapM (·.materializeAsync)
  tasks.foldlM (fun tr t => return mixTrace tr <| ← await t) nilTrace

def materializeArray [Await n m] (targets : Array (Target i m n t)) :  m t := do
  let tasks ← targets.mapM (·.materializeAsync)
  tasks.foldlM (fun tr t => return mixTrace tr <| ← await t) nilTrace

variable [Pure n]  [BindAsync m n]

def materializeListAsync  (targets : List (Target i m n t)) : m (n t) := do
  foldlListAsync mixTraceM nilTrace (← targets.mapM (·.materializeAsync))

def materializeArrayAsync (targets : Array (Target i m n t)) :  m (n t) := do
  foldlArrayAsync mixTraceM nilTrace (← targets.mapM (·.materializeAsync))

def collectList (targets : List (Target i m n t)) : Target (List i) m n t :=
  mk (targets.map (·.info)) <| materializeListAsync targets

def collectArray (targets : Array (Target i m n t)) : Target (Array i) m n t :=
  mk (targets.map (·.info))  <| materializeArrayAsync targets

def collectOpaqueList (targets : List (Target i m n t)) : Target PUnit m n t :=
  opaque <| materializeListAsync targets

def collectOpaqueArray (targets : Array (Target i m n t)) : Target PUnit m n t :=
  opaque <| materializeArrayAsync targets

end
end Target
