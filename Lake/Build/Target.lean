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

def opaque (task : k t) : ActiveTarget PUnit k t :=
  ⟨(), task⟩

protected def pure [Pure k] (info : i) (trace : t) : ActiveTarget i k t :=
  ⟨info, pure trace⟩

def nil [NilTrace t] [Pure k] : ActiveTarget PUnit k t :=
  mk () <| pure nilTrace

protected def mapAsync [BindAsync' m n k] [MonadLiftT n m] (self : ActiveTarget i k α) (f : i → α → m β) : m (k β) :=
  liftM <| bindAsync' self.task (f self.info)

protected def mapOpaqueAsync [BindAsync' m n k] [MonadLiftT n m] (self : ActiveTarget i k α) (f : α → m β) : m (k β) :=
  liftM <| bindAsync' self.task f

protected def bindAsync [BindAsync n k] [MonadLiftT n m] (self : ActiveTarget i k α) (f : i → α → n (k β)) : m (k β) :=
  liftM <| bindAsync self.task (f self.info)

protected def bindOpaqueAsync [BindAsync n k] [MonadLiftT n m] (self : ActiveTarget i k α) (f : α → n (k β)) : m (k β) :=
  liftM <| bindAsync self.task f

def materialize [Await k m'] [MonadLiftT m' m] (self : ActiveTarget i k t) : m t :=
  liftM <| await self.task

def build [Await k m'] [MonadLiftT m' m] [Functor m] (self : ActiveTarget i k t) : m i :=
  Functor.mapConst self.info self.materialize

def buildOpaque [Await k m'] [MonadLiftT m' m] [Functor m] (self : ActiveTarget i k t) : m PUnit :=
  discard <| self.materialize

def mixOpaqueAsync
[MixTrace t] [SeqMapAsync n k] [MonadLiftT n m] [Monad m]
(t1 : ActiveTarget α k t) (t2 : ActiveTarget β k t) : m (ActiveTarget PUnit k t) := do
  ActiveTarget.opaque <| ← liftM <| seqMapAsync mixTrace t1.task t2.task

section
variable [NilTrace t] [MixTrace t]

def materializeList [Await k n] [MonadLiftT n m] [Monad m] (targets : List (ActiveTarget i k t)) : m t := do
  targets.foldlM (fun tr t => return mixTrace tr <| ← liftM <| await t.task) nilTrace

def materializeArray [Await k n] [MonadLiftT n m] [Monad m] (targets : Array (ActiveTarget i k t)) : m t := do
  targets.foldlM (fun tr t => return mixTrace tr <| ← liftM <| await t.task) nilTrace

variable [SeqMapAsync n k] [Monad n] [MonadLiftT n m] [Monad m] [Pure k]

def collectList (targets : List (ActiveTarget i k t)) : m (ActiveTarget (List i) k t) := do
  mk (targets.map (·.info)) <| ← liftM <| foldRightListAsync mixTrace nilTrace <| targets.map (·.task)

def collectArray (targets : Array (ActiveTarget i k t)) : m (ActiveTarget (Array i) k t) := do
  mk (targets.map (·.info)) <| ← liftM <| foldRightArrayAsync mixTrace nilTrace <| targets.map (·.task)

def collectOpaqueList (targets : List (ActiveTarget i k t)) : m (ActiveTarget PUnit k t) := do
  opaque <| ← liftM <| foldRightListAsync mixTrace nilTrace <| targets.map (·.task)

def collectOpaqueArray (targets : Array (ActiveTarget i k t)) : m (ActiveTarget PUnit k t) := do
  opaque <| ← liftM <| foldRightArrayAsync mixTrace nilTrace <| targets.map (·.task)

end
end ActiveTarget

--------------------------------------------------------------------------------
-- # Inactive Target
--------------------------------------------------------------------------------

structure Target.{u,v,v',w} (i : Type u) (m : Type v → Type w) (k : Type v' → Type v) (t : Type v') where
  info : i
  task : m (k t)

instance [Inhabited i] [Inhabited t] [Pure m] [Pure k] : Inhabited (Target i m k t) :=
  ⟨Inhabited.default, pure (pure Inhabited.default)⟩

namespace Target

def withInfo (info : i') (self : Target i m k t) : Target i' m k t :=
  {self with info}

def withoutInfo (self : Target i m k t) : Target PUnit m k t :=
  self.withInfo ()

def withTask (task : m' (k' t')) (self : Target i m k t) : Target i m' k' t' :=
  {self with task}

def opaque (task : m (k t)) : Target PUnit m k t :=
  mk () task

def opaqueAsync [Async m n k] [MonadLiftT n n'] (act : m t) : Target PUnit n' k t :=
  mk () (liftM <| async act)

protected def async [Async m n k] [MonadLiftT n n'] (info : i) (act : m t) : Target i n' k t :=
  mk info (liftM <| async act)

def active [Pure m] (target : ActiveTarget i k t) : Target i m k t :=
  mk target.info <| pure target.task

protected def pure [Pure m] [Pure k] (info : i) (trace : t) : Target i m k t :=
  mk info <| pure <| pure trace

def nil [NilTrace t] [Pure m] [Pure k] : Target PUnit m k t :=
  mk () <| pure <| pure nilTrace

def computeSync [ComputeTrace i m' t] [MonadLiftT m' m] [Functor m] [Pure k] (info : i) : Target i m k t :=
  mk info <| pure <$> computeTrace info

def computeAsync [ComputeTrace i m' t] [MonadLiftT m' m] [Async m n k] [MonadLiftT n m]  (info : i) : Target i m k t :=
  mk info <| liftM <| async <| liftM (n := m) <| ComputeTrace.computeTrace info

def activate [Functor m] (self : Target i m k t) : m (ActiveTarget i k t) :=
  Functor.map (fun t => ActiveTarget.mk self.info t) self.task

def materializeAsync (self : Target i m k t) : m (k t) :=
  self.task

def materialize [Await k n] [MonadLiftT n m] [Bind m] (self : Target i m k t) : m t := do
  self.task >>= (liftM ∘ await)

def build  [Await k n] [MonadLiftT n m] [Functor m] [Bind m] (self : Target i m k t) : m i := do
  Functor.mapConst self.info self.materialize

def buildOpaque  [Await k n] [MonadLiftT n m] [Functor m] [Bind m] (self : Target i m k t) : m PUnit := do
  discard self.materialize

def buildAsync [Functor m] [Functor k] (self : Target i m k t) : m (k i) :=
  Functor.mapConst self.info <$> self.task

def buildOpaqueAsync [Functor m] [Functor k] (self : Target i m k t) : m (k PUnit) :=
  discard <$> self.task

protected def mapAsync [BindAsync' m n k] [MonadLiftT n m] [Bind m] (self : Target i m k α) (f : i → α → m β) : m (k β) :=
  self.task >>= fun tk => liftM <| bindAsync' tk (f self.info)

protected def mapOpaqueAsync [BindAsync' m n k] [MonadLiftT n m] [Bind m] (self : Target i m k α) (f : α → m β) : m (k β) :=
  self.task >>= fun tk => liftM <| bindAsync' tk f

protected def bindAsync [BindAsync n k] [MonadLiftT n m] [Bind m] (self : Target i m k α) (f : i → α → n (k β)) : m (k β) :=
  self.task >>= fun tk => liftM <| bindAsync tk (f self.info)

protected def bindOpaqueAsync [BindAsync n k] [MonadLiftT n m] [Bind m] (self : Target i m k α) (f : α → n (k β)) : m (k β) :=
  self.task >>= fun tk => liftM <| bindAsync tk f

def mixOpaqueAsync
[MixTrace t] [SeqMapAsync n k] [MonadLiftT n m] [Monad m]
(t1 :  Target α m k t) (t2 :  Target β m k t) : Target PUnit m k t :=
  Target.opaque do
    let tk1 ← t1.materializeAsync
    let tk2 ← t2.materializeAsync
    liftM <| seqMapAsync mixTrace tk1 tk2

section
variable [NilTrace t] [MixTrace t]

def materializeList [Await k n] [MonadLiftT n m] [Monad m] (targets : List (Target i m k t)) : m t := do
  let tasks ← targets.mapM (·.materializeAsync)
  tasks.foldlM (fun tr t => return mixTrace tr <| ← liftM <| await t) nilTrace

def materializeArray [Await k n] [MonadLiftT n m] [Monad m] (targets : Array (Target i m k t)) :  m t := do
  let tasks ← targets.mapM (·.materializeAsync)
  tasks.foldlM (fun tr t => return mixTrace tr <| ← liftM <| await t) nilTrace

variable [SeqMapAsync n k] [Monad n] [MonadLiftT n m] [Monad m] [Pure k]

def materializeListAsync (targets : List (Target i m k t)) : m (k t) := do
  liftM <| foldRightListAsync mixTrace nilTrace (← targets.mapM (·.materializeAsync))

def materializeArrayAsync (targets : Array (Target i m k t)) : m (k t) := do
   liftM <| foldRightArrayAsync mixTrace nilTrace (← targets.mapM (·.materializeAsync))

def collectList (targets : List (Target i m k t)) : Target (List i) m k t :=
  mk (targets.map (·.info)) <| materializeListAsync targets

def collectArray (targets : Array (Target i m k t)) : Target (Array i) m k t :=
  mk (targets.map (·.info)) <| materializeArrayAsync targets

def collectOpaqueList (targets : List (Target i m k t)) : Target PUnit m k t :=
  opaque <| materializeListAsync targets

def collectOpaqueArray (targets : Array (Target i m k t)) : Target PUnit m k t :=
  opaque <| materializeArrayAsync targets

end
end Target
