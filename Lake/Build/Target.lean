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
/-! # Active Targets -/
--------------------------------------------------------------------------------

structure ActiveTarget.{u,v} (ι : Type u) (k : Type u → Type v) (τ : Type u) where
  task : k (ι × τ)

instance [Inhabited ι] [Inhabited τ] [Pure k] : Inhabited (ActiveTarget ι k τ) :=
  ⟨⟨pure default⟩⟩

namespace ActiveTarget

def withoutInfo [Functor k] (target :  ActiveTarget ι k t) : ActiveTarget PUnit k t :=
  mk <| (fun (_,t) => ((),t)) <$> target.task

def «opaque» [Functor k] (task : k t) : ActiveTarget PUnit k t :=
  mk <| ((), ·) <$> task

protected def pure [Pure k] (info : ι) (trace : τ) : ActiveTarget ι k τ :=
  mk <| pure (info, trace)

def nil [NilTrace τ] [Pure k] : ActiveTarget PUnit k τ :=
  mk <| pure ((), nilTrace)

protected def bindSync [BindSync m n k] (self : ActiveTarget ι k α) (f : ι → α → m β) : n (k β) :=
  bindSync self.task fun (i, a) => f i a

protected def bindOpaqueSync [BindSync m n k] (self : ActiveTarget ι k α) (f : α → m β) : n (k β) :=
  bindSync self.task fun (_, a) => f a

protected def bindAsync [BindAsync n k] (self : ActiveTarget ι k α) (f : ι → α → n (k β)) : n (k β) :=
  bindAsync self.task fun (i, a) => f i a

protected def bindOpaqueAsync [BindAsync n k] (self : ActiveTarget ι k α) (f : α → n (k β)) : n (k β) :=
  bindAsync self.task fun (_, a) => f a

def materialize [Await k n] [MonadLiftT n m] [Functor m] (self : ActiveTarget ι k τ) : m τ :=
  (·.2) <$> liftM (await self.task)

def materializeAsync [Functor k] (self : ActiveTarget ι k τ) : k τ :=
  (·.2) <$> self.task

def build [Await k n] [MonadLiftT n m] [Functor m] (self : ActiveTarget ι k τ) : m ι :=
  (·.1) <$> liftM (await self.task)

def buildOpaque [Await k n] [MonadLiftT n m] [Functor m] (self : ActiveTarget ι k τ) : m PUnit :=
  discard <| self.materialize

def mixOpaqueAsync
[MixTrace τ] [SeqWithAsync n k] [MonadLiftT n m] [Monad m]
(t1 : ActiveTarget α k τ) (t2 : ActiveTarget β k τ) : m (ActiveTarget PUnit k τ) := do
  pure <| mk <| ← liftM <| seqWithAsync (fun (_,t) (_,t') => ((), mixTrace t t')) t1.task t2.task

section
variable [NilTrace τ] [MixTrace τ]

def materializeList [Await k n] [MonadLiftT n m] [Monad m] (targets : List (ActiveTarget ι k τ)) : m τ := do
  targets.foldlM (fun tr t => return mixTrace tr <| ← t.materialize) nilTrace

def materializeArray [Await k n] [MonadLiftT n m] [Monad m] (targets : Array (ActiveTarget ι k τ)) : m τ := do
  targets.foldlM (fun tr t => return mixTrace tr <| ← t.materialize) nilTrace

variable [SeqWithAsync n k] [Monad n] [MonadLiftT n m] [Monad m] [Pure k]

def collectList (targets : List (ActiveTarget ι k τ)) : m (ActiveTarget (List ι) k τ) := mk <$> do
  liftM <| foldLeftListAsync (fun (i,t') (a,t) => (i :: a, mixTrace t t')) ([], nilTrace) <| targets.map (·.task)

def collectArray (targets : Array (ActiveTarget ι k τ)) : m (ActiveTarget (Array ι) k τ) := mk <$> do
  liftM <| foldRightArrayAsync (fun (a,t) (i,t') => (a.push i, mixTrace t t')) (#[], nilTrace) <| targets.map (·.task)

variable [Functor k]

def collectOpaqueList (targets : List (ActiveTarget ι k τ)) : m (ActiveTarget PUnit k τ) := «opaque» <$> do
  liftM <| foldLeftListAsync (fun (_,t') t => mixTrace t t') nilTrace <| targets.map (·.task)

def collectOpaqueArray (targets : Array (ActiveTarget ι k τ)) : m (ActiveTarget PUnit k τ) := «opaque» <$> do
  liftM <| foldRightArrayAsync (fun t (_,t') => mixTrace t t') nilTrace <| targets.map (·.task)

end
end ActiveTarget

--------------------------------------------------------------------------------
/-! # Inactive Target -/
--------------------------------------------------------------------------------

structure Target.{u,v,w} (ι : Type u) (n : Type v → Type w) (k : Type u → Type v) (τ : Type u) where
  task : n (k (ι × τ))

instance [Inhabited ι] [Inhabited τ] [Pure n] [Pure k] : Inhabited (Target ι n k τ) :=
  ⟨⟨pure (pure default)⟩⟩

namespace Target

def «opaque» [Functor n] [Functor k] (task : n (k τ)) : Target PUnit n k τ :=
  mk <| ((fun t => ((), t)) <$> ·) <$> task

def opaqueSync [Sync m n k] [Functor m] (act : m τ) : Target PUnit n k τ :=
  mk <| sync <| ((), ·) <$> act

def opaqueAsync [Async m n k] [Functor m] (act : m τ) : Target PUnit n k τ :=
  mk <| async <| ((), ·) <$> act

protected def sync [Sync m n k] [Functor m] (info : ι) (act : m τ) : Target ι n k τ :=
  mk <| sync <| (info, ·) <$> act

protected def async [Async m n k] [Functor m] (info : ι) (act : m τ) : Target ι n k τ :=
  mk <| async <| (info, ·) <$> act

def active [Pure n] (target : ActiveTarget ι k τ) : Target ι n k τ :=
  mk <| pure target.task

protected def pure [Pure n] [Pure k] (info : ι) (trace : τ) : Target ι n k τ :=
  mk <| pure <| pure (info, trace)

def nil [NilTrace τ] [Pure n] [Pure k] : Target PUnit n k τ :=
  mk <| pure <| pure <| ((), nilTrace)

def computeSync [Functor m] [ComputeTrace ι m τ] [Sync m n k] (info : ι) : Target ι n k τ :=
  mk <| sync <| (info, ·) <$> ComputeTrace.computeTrace info

def computeAsync [Functor m]  [ComputeTrace ι m τ] [Async m n k] (info : ι) : Target ι n k τ :=
  mk <| async <| (info, ·) <$> ComputeTrace.computeTrace info

def activate [Functor n] (self : Target ι n k τ) : n (ActiveTarget ι k τ) :=
  (.mk ·) <$> self.task

def materializeAsync [Functor n] [Functor k] (self : Target ι n k τ) : n (k τ) :=
  ((·.2) <$> ·) <$> self.task

def materialize [Await k m'] [MonadLiftT m' m] [MonadLiftT n m] [Functor m] [Bind m] (self : Target ι n k τ) : m τ :=
  liftM self.task >>= fun t => (·.2) <$> liftM (await t)

def build [Await k m'] [MonadLiftT m' m] [MonadLiftT n m] [Functor m] [Bind m] (self : Target ι n k τ) : m ι :=
  liftM self.task >>= fun t => (·.1) <$> liftM (await t)

def buildOpaque [Await k m'] [MonadLiftT m' m] [MonadLiftT n m] [Functor m] [Bind m] (self : Target ι n k τ) : m PUnit :=
  discard self.materialize

def buildAsync [Functor n] [Functor k] (self : Target ι n k τ) : n (k ι) :=
  ((·.1) <$> ·) <$> self.task

def buildOpaqueAsync [Functor n] [Functor k] (self : Target ι n k τ) : n (k PUnit) :=
  discard <$> self.task

protected def bindSync [BindSync m n k] [Bind n] (self : Target ι n k τ) (f : ι → τ → m β) : n (k β) :=
  self.task >>= fun tk => bindSync tk fun (i,t) => f i t

protected def bindOpaqueSync [BindSync m n k] [Bind n] (self : Target ι n k τ) (f : τ → m β) : n (k β) :=
  self.task >>= fun tk => bindSync tk fun (_,t) => f t

protected def bindAsync [BindAsync n k] [Bind n] (self : Target ι n k τ) (f : ι → τ → n (k β)) : n (k β) :=
  self.task >>= fun tk => bindAsync tk fun (i,t) => f i t

protected def bindOpaqueAsync [BindAsync n k] [Bind n] (self : Target ι n k τ) (f : τ → n (k β)) : n (k β) :=
  self.task >>= fun tk => bindAsync tk fun (_,t) => f t

def mixOpaqueAsync
[MixTrace τ] [SeqWithAsync n k] [Functor k] [Monad n]
(t1 : Target α n k τ) (t2 :  Target β n k τ) : Target PUnit n k τ :=
  mk do
    let tk1 ← t1.materializeAsync
    let tk2 ← t2.materializeAsync
    ((fun t => ((),t)) <$> ·) <$> seqWithAsync mixTrace tk1 tk2

section
variable [NilTrace τ] [MixTrace τ]

def materializeList [Await k m] [MonadLiftT n m] [Monad m] (targets : List (Target ι n k τ)) : m τ := do
  let tasks ← targets.mapM (·.task)
  tasks.foldlM (fun tr τ => return mixTrace tr (← liftM <| await τ).2) nilTrace

def materializeArray [Await k m] [MonadLiftT n m] [Monad m] (targets : Array (Target ι n k τ)) : m τ := do
  let tasks ← targets.mapM (·.task)
  tasks.foldlM (fun tr τ => return mixTrace tr (← liftM <| await τ).2) nilTrace

variable [SeqWithAsync n' k] [Monad n'] [MonadLiftT n' n] [Monad n] [Pure k] [Functor k]

def materializeListAsync (targets : List (Target ι n k τ)) : n (k τ) := do
  liftM <| foldRightListAsync mixTrace nilTrace (← targets.mapM (·.materializeAsync))

def materializeArrayAsync (targets : Array (Target ι n k τ)) : n (k τ) := do
  liftM <| foldRightArrayAsync mixTrace nilTrace (← targets.mapM (·.materializeAsync))

def collectList (targets : List (Target ι n k τ)) : Target (List ι) n k τ :=
  mk do
    let tasks ← targets.mapM (·.task)
    liftM <| foldLeftListAsync (fun (i,t') (a,t) => (i :: a, mixTrace t t')) ([], nilTrace) tasks

def collectArray (targets : Array (Target ι n k τ)) : Target (Array ι) n k τ :=
  mk do
    let tasks ← targets.mapM (·.task)
    liftM <| foldRightArrayAsync (fun (a,t) (i,t') => (a.push i, mixTrace t t')) (#[], nilTrace) tasks

def collectOpaqueList (targets : List (Target ι n k τ)) : Target PUnit n k τ :=
  mk <| ((fun t => ((), t)) <$> ·) <$> materializeListAsync targets

def collectOpaqueArray (targets : Array (Target ι n k τ)) : Target PUnit n k τ :=
  mk <| ((fun t => ((), t)) <$> ·) <$> materializeArrayAsync targets

end
end Target
