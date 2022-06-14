/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Util.Async
import Lake.Build.Trace

open System
namespace Lake

--------------------------------------------------------------------------------
-- # Active Targets
--------------------------------------------------------------------------------

structure ActiveTarget.{u,v,w} (i : Type u) (k : Type v → Type w) (t : Type v) where
  info : i
  task : k t

instance [Inhabited i] [Inhabited t] [Pure k] : Inhabited (ActiveTarget i k t) :=
  ⟨Inhabited.default, pure Inhabited.default⟩

namespace ActiveTarget

def withInfo (info : i') (self : ActiveTarget i k t) : ActiveTarget i' k t :=
  {self with info}

def withoutInfo (self : ActiveTarget i k t) : ActiveTarget PUnit k t :=
  self.withInfo ()

def withTask (task : k' t') (self : ActiveTarget i k t) : ActiveTarget i k' t' :=
  {self with task}

def «opaque» (task : k t) : ActiveTarget PUnit k t :=
  ⟨(), task⟩

protected def pure [Pure k] (info : i) (trace : t) : ActiveTarget i k t :=
  ⟨info, pure trace⟩

def nil [NilTrace t] [Pure k] : ActiveTarget PUnit k t :=
  mk () <| pure nilTrace

protected def bindSync [BindSync m n k] (self : ActiveTarget i k α) (f : i → α → m β) : n (k β) :=
  bindSync self.task (f self.info)

protected def bindOpaqueSync [BindSync m n k] (self : ActiveTarget i k α) (f : α → m β) : n (k β) :=
  bindSync self.task f

protected def bindAsync [BindAsync n k] (self : ActiveTarget i k α) (f : i → α → n (k β)) : n (k β) :=
  bindAsync self.task (f self.info)

protected def bindOpaqueAsync [BindAsync n k] (self : ActiveTarget i k α) (f : α → n (k β)) : n (k β) :=
  bindAsync self.task f

def materialize [Await k m'] [MonadLiftT m' m] (self : ActiveTarget i k t) : m t :=
  liftM <| await self.task

def build [Await k m'] [MonadLiftT m' m] [Functor m] (self : ActiveTarget i k t) : m i :=
  Functor.mapConst self.info self.materialize

def buildOpaque [Await k m'] [MonadLiftT m' m] [Functor m] (self : ActiveTarget i k t) : m PUnit :=
  discard <| self.materialize

def mixOpaqueAsync
[MixTrace t] [SeqWithAsync n k] [MonadLiftT n m] [Monad m]
(t1 : ActiveTarget α k t) (t2 : ActiveTarget β k t) : m (ActiveTarget PUnit k t) := do
  pure <| ActiveTarget.opaque <| ← liftM <| seqWithAsync mixTrace t1.task t2.task

section
variable [NilTrace t] [MixTrace t]

def materializeList [Await k n] [MonadLiftT n m] [Monad m] (targets : List (ActiveTarget i k t)) : m t := do
  targets.foldlM (fun tr t => return mixTrace tr <| ← liftM <| await t.task) nilTrace

def materializeArray [Await k n] [MonadLiftT n m] [Monad m] (targets : Array (ActiveTarget i k t)) : m t := do
  targets.foldlM (fun tr t => return mixTrace tr <| ← liftM <| await t.task) nilTrace

variable [SeqWithAsync n k] [Monad n] [MonadLiftT n m] [Monad m] [Pure k]

def collectList (targets : List (ActiveTarget i k t)) : m (ActiveTarget (List i) k t) := do
  pure <| mk (targets.map (·.info)) <| ← liftM <| foldRightListAsync mixTrace nilTrace <| targets.map (·.task)

def collectArray (targets : Array (ActiveTarget i k t)) : m (ActiveTarget (Array i) k t) := do
  pure <| mk (targets.map (·.info)) <| ← liftM <| foldRightArrayAsync mixTrace nilTrace <| targets.map (·.task)

def collectOpaqueList (targets : List (ActiveTarget i k t)) : m (ActiveTarget PUnit k t) := do
  pure <| «opaque» <| ← liftM <| foldRightListAsync mixTrace nilTrace <| targets.map (·.task)

def collectOpaqueArray (targets : Array (ActiveTarget i k t)) : m (ActiveTarget PUnit k t) := do
  pure <| «opaque» <| ← liftM <| foldRightArrayAsync mixTrace nilTrace <| targets.map (·.task)

end
end ActiveTarget

--------------------------------------------------------------------------------
-- # Inactive Target
--------------------------------------------------------------------------------

structure Target.{u,v,v',w} (i : Type u) (n : Type v → Type w) (k : Type v' → Type v) (t : Type v') where
  info : i
  task : n (k t)

instance [Inhabited i] [Inhabited t] [Pure n] [Pure k] : Inhabited (Target i n k t) :=
  ⟨Inhabited.default, pure <| pure Inhabited.default⟩

namespace Target

def withInfo (info : i') (self : Target i n k t) : Target i' n k t :=
  {self with info}

def withoutInfo (self : Target i n k t) : Target PUnit n k t :=
  self.withInfo ()

def withTask (task : n' (k' t')) (self : Target i n k t) : Target i n' k' t' :=
  {self with task}

def «opaque» (task : n (k t)) : Target PUnit n k t :=
  mk () task

def opaqueSync [Sync m n k] (act : m t) : Target PUnit n k t :=
  mk () <| sync act

def opaqueAsync [Async m n k] (act : m t) : Target PUnit n k t :=
  mk () <| async act

protected def sync [Sync m n k] (info : i) (act : m t) : Target i n k t :=
  mk info <| sync act

protected def async [Async m n k] (info : i) (act : m t) : Target i n k t :=
  mk info <| async act

def active [Pure n] (target : ActiveTarget i k t) : Target i n k t :=
  mk target.info <| pure target.task

protected def pure [Pure n] [Pure k] (info : i) (trace : t) : Target i n k t :=
  mk info <| pure <| pure trace

def nil [NilTrace t] [Pure n] [Pure k] : Target PUnit n k t :=
  mk () <| pure <| pure <| nilTrace

def computeSync [ComputeTrace i m t] [Sync m n k] (info : i) : Target i n k t :=
  mk info <| sync <| ComputeTrace.computeTrace info

def computeAsync [ComputeTrace i m t] [Async m n k] (info : i) : Target i n k t :=
  mk info <| async <| ComputeTrace.computeTrace info

def activate [Functor n] (self : Target i n k t) : n (ActiveTarget i k t) :=
  Functor.map (fun t => ActiveTarget.mk self.info t) self.task

def materializeAsync (self : Target i n k t) : n (k t) :=
  self.task

def materialize [Await k m'] [MonadLiftT m' m] [MonadLiftT n m] [Bind m] (self : Target i n k t) : m t :=
  liftM self.task >>= (liftM ∘ await)

def build [Await k m'] [MonadLiftT m' m] [MonadLiftT n m] [Functor m] [Bind m] (self : Target i n k t) : m i :=
  Functor.mapConst self.info self.materialize

def buildOpaque [Await k m'] [MonadLiftT m' m] [MonadLiftT n m] [Functor m] [Bind m] (self : Target i n k t) : m PUnit :=
  discard self.materialize

def buildAsync [Functor n] [Functor k] (self : Target i n k t) : n (k i) :=
  Functor.mapConst self.info <$> self.task

def buildOpaqueAsync [Functor n] [Functor k] (self : Target i n k t) : n (k PUnit) :=
  discard <$> self.task

protected def bindSync [BindSync m n k] [Bind n] (self : Target i n k t) (f : i → t → m β) : n (k β) :=
  self.task >>= fun tk => bindSync tk (f self.info)

protected def bindOpaqueSync [BindSync m n k] [Bind n] (self : Target i n k t) (f : t → m β) : n (k β) :=
  self.task >>= fun tk => bindSync tk f

protected def bindAsync [BindAsync n k] [Bind n] (self : Target i n k t) (f : i → t → n (k β)) : n (k β) :=
  self.task >>= fun tk => bindAsync tk (f self.info)

protected def bindOpaqueAsync [BindAsync n k] [Bind n] (self : Target i n k t) (f : t → n (k β)) : n (k β) :=
  self.task >>= fun tk => bindAsync tk f

def mixOpaqueAsync
[MixTrace t] [SeqWithAsync n k] [Monad n]
(t1 : Target α n k t) (t2 :  Target β n k t) : Target PUnit n k t :=
  Target.opaque do
    let tk1 ← t1.materializeAsync
    let tk2 ← t2.materializeAsync
    seqWithAsync mixTrace tk1 tk2

section
variable [NilTrace t] [MixTrace t]

def materializeList [Await k m] [MonadLiftT n m] [Monad m] (targets : List (Target i n k t)) : m t := do
  let tasks ← targets.mapM (·.materializeAsync)
  tasks.foldlM (fun tr t => return mixTrace tr <| ← liftM <| await t) nilTrace

def materializeArray [Await k m] [MonadLiftT n m] [Monad m] (targets : Array (Target i n k t)) : m t := do
  let tasks ← targets.mapM (·.materializeAsync)
  tasks.foldlM (fun tr t => return mixTrace tr <| ← liftM <| await t) nilTrace

variable [SeqWithAsync n' k] [Monad n'] [MonadLiftT n' n] [Monad n] [Pure k]

def materializeListAsync (targets : List (Target i n k t)) : n (k t) := do
  liftM <| foldRightListAsync mixTrace nilTrace (← targets.mapM (·.materializeAsync))

def materializeArrayAsync (targets : Array (Target i n k t)) : n (k t) := do
  liftM <| foldRightArrayAsync mixTrace nilTrace (← targets.mapM (·.materializeAsync))

def collectList (targets : List (Target i n k t)) : Target (List i) n k t :=
  mk (targets.map (·.info)) <| materializeListAsync targets

def collectArray (targets : Array (Target i n k t)) : Target (Array i) n k t :=
  mk (targets.map (·.info)) <| materializeArrayAsync targets

def collectOpaqueList (targets : List (Target i n k t)) : Target PUnit n k t :=
  «opaque» <| materializeListAsync targets

def collectOpaqueArray (targets : Array (Target i n k t)) : Target PUnit n k t :=
  «opaque» <| materializeArrayAsync targets

end
end Target
