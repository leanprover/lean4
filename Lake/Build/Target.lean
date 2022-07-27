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

def ActiveTarget.{u,v} (ι : Type u) (k : Type u → Type v) (τ : Type u) :=
  k (ι × τ)

namespace ActiveTarget

@[inline] def  mk (task : k (ι × τ)) : ActiveTarget ι k τ :=
  task

@[inline] def  task (target : ActiveTarget ι k τ) : k (ι × τ) :=
  target

instance [Inhabited ι] [Inhabited τ] [Pure k] : Inhabited (ActiveTarget ι k τ) :=
  ⟨mk <| pure default⟩

@[inline] def «opaque» [Functor k] (task : k t) : ActiveTarget PUnit k t :=
  mk <| ((), ·) <$> task

@[inline] def nil [NilTrace τ] [Pure k] : ActiveTarget PUnit k τ :=
  mk <| pure ((), nilTrace)

@[inline] protected def bindSync [BindSync m n k]
(self : ActiveTarget ι k α) (f : ι → α → m β) : n (k β) :=
  bindSync self fun (i, a) => f i a

@[inline] protected def bindOpaqueSync [BindSync m n k]
(self : ActiveTarget ι k α) (f : α → m β) : n (k β) :=
  bindSync self fun (_, a) => f a

@[inline] protected def bindAsync [BindAsync n k]
(self : ActiveTarget ι k α) (f : ι → α → n (k β)) : n (k β) :=
  bindAsync self fun (i, a) => f i a

@[inline] protected def bindOpaqueAsync [BindAsync n k]
(self : ActiveTarget ι k α) (f : α → n (k β)) : n (k β) :=
  bindAsync self fun (_, a) => f a

@[inline] def build
[Await k n] [MonadLiftT n m] [Functor m] (self : ActiveTarget ι k τ) : m ι :=
  (·.1) <$> liftM (await self.task)

@[inline] def buildOpaque
[Await k n] [MonadLiftT n m] [Functor m] (self : ActiveTarget ι k τ) : m PUnit :=
  discard <| liftM (await self.task)

variable [MixTrace τ] [SeqWithAsync n k] [MonadLiftT n m] [Monad m]

def mixOpaqueAsync
(t1 : ActiveTarget α k τ) (t2 : ActiveTarget β k τ) : m (ActiveTarget PUnit k τ) :=
  mk <$> liftM (seqWithAsync (fun (_,t) (_,t') => ((), mixTrace t t')) t1 t2)

variable [NilTrace τ] [Monad n] [Pure k]

def collectList (targets : List (ActiveTarget ι k τ)) : m (ActiveTarget (List ι) k τ) := mk <$> do
  liftM <| foldLeftListAsync (fun (i,t') (a,t) => (i :: a, mixTrace t t')) ([], nilTrace) targets

def collectArray (targets : Array (ActiveTarget ι k τ)) : m (ActiveTarget (Array ι) k τ) := mk <$> do
  liftM <| foldRightArrayAsync (fun (a,t) (i,t') => (a.push i, mixTrace t t')) (#[], nilTrace) targets

variable [Functor k]

def collectOpaqueList (targets : List (ActiveTarget ι k τ)) : m (ActiveTarget PUnit k τ) := «opaque» <$> do
  liftM <| foldLeftListAsync (fun (_,t') t => mixTrace t t') nilTrace targets

def collectOpaqueArray (targets : Array (ActiveTarget ι k τ)) : m (ActiveTarget PUnit k τ) := «opaque» <$> do
  liftM <| foldRightArrayAsync (fun t (_,t') => mixTrace t t') nilTrace targets

end ActiveTarget

--------------------------------------------------------------------------------
/-! # Inactive Target -/
--------------------------------------------------------------------------------

structure Target.{u,v,w} (ι : Type u) (n : Type v → Type w) (k : Type u → Type v) (τ : Type u) where
  task : n (k (ι × τ))

instance [Inhabited ι] [Inhabited τ] [Pure n] [Pure k] : Inhabited (Target ι n k τ) :=
  ⟨⟨pure (pure default)⟩⟩

namespace Target

@[inline] def active [Pure n] (target : ActiveTarget ι k τ) : Target ι n k τ :=
  mk <| pure target

@[inline] def nil [NilTrace τ] [Pure n] [Pure k] : Target PUnit n k τ :=
  mk <| pure <| pure <| ((), nilTrace)

@[inline] def activate [Functor n] (self : Target ι n k τ) : n (ActiveTarget ι k τ) :=
  (.mk ·) <$> self.task

@[inline] def materializeAsync [Functor n] [Functor k] (self : Target ι n k τ) : n (k τ) :=
  ((·.2) <$> ·) <$> self.task

def materialize [Await k m'] [MonadLiftT m' m] [MonadLiftT n m] [Functor m] [Bind m] (self : Target ι n k τ) : m τ :=
  liftM self.task >>= fun t => (·.2) <$> liftM (await t)

@[inline] protected def bindSync [BindSync m n k] [Bind n]
(self : Target ι n k τ) (f : ι → τ → m β) : n (k β) :=
  self.task >>= fun tk => bindSync tk fun (i,t) => f i t

@[inline] protected def bindOpaqueSync
[BindSync m n k] [Bind n] (self : Target ι n k τ) (f : τ → m β) : n (k β) :=
  self.task >>= fun tk => bindSync tk fun (_,t) => f t

@[inline] protected def bindAsync
[BindAsync n k] [Bind n] (self : Target ι n k τ) (f : ι → τ → n (k β)) : n (k β) :=
  self.task >>= fun tk => bindAsync tk fun (i,t) => f i t

@[inline] protected def bindOpaqueAsync
[BindAsync n k] [Bind n] (self : Target ι n k τ) (f : τ → n (k β)) : n (k β) :=
  self.task >>= fun tk => bindAsync tk fun (_,t) => f t

def mixOpaqueAsync
[MixTrace τ] [SeqWithAsync n k] [Functor k] [Monad n]
(t1 : Target α n k τ) (t2 :  Target β n k τ) : Target PUnit n k τ := mk do
  let tk1 ← t1.materializeAsync
  let tk2 ← t2.materializeAsync
  ((fun t => ((),t)) <$> ·) <$> seqWithAsync mixTrace tk1 tk2

section
variable [NilTrace τ] [MixTrace τ]
variable [SeqWithAsync n' k] [Monad n'] [MonadLiftT n' n] [Monad n] [Pure k] [Functor k]

def materializeListAsync (targets : List (Target ι n k τ)) : n (k τ) := do
  liftM <| foldRightListAsync mixTrace nilTrace (← targets.mapM (·.materializeAsync))

def materializeArrayAsync (targets : Array (Target ι n k τ)) : n (k τ) := do
  liftM <| foldRightArrayAsync mixTrace nilTrace (← targets.mapM (·.materializeAsync))

def collectList (targets : List (Target ι n k τ)) : Target (List ι) n k τ := mk do
  let tasks ← targets.mapM (·.task)
  let f := fun (i,t') (a,t) => (i :: a, mixTrace t t')
  liftM <| foldLeftListAsync f ([], nilTrace) tasks

def collectArray (targets : Array (Target ι n k τ)) : Target (Array ι) n k τ := mk do
  let tasks ← targets.mapM (·.task)
  let f := fun (a,t) (i,t') => (a.push i, mixTrace t t')
  liftM <| foldRightArrayAsync f (#[], nilTrace) tasks

def collectOpaqueList (targets : List (Target ι n k τ)) : Target PUnit n k τ :=
  mk <| ((fun t => ((), t)) <$> ·) <$> materializeListAsync targets

def collectOpaqueArray (targets : Array (Target ι n k τ)) : Target PUnit n k τ :=
  mk <| ((fun t => ((), t)) <$> ·) <$> materializeArrayAsync targets

end
end Target
