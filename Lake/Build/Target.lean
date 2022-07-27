/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Util.Async
import Lake.Build.Trace

open System
namespace Lake

structure Target.{u,v,w} (α : Type u) (n : Type v → Type w) (k : Type u → Type v) (τ : Type u) where
  task : n (k (α × τ))

instance [Inhabited α] [Inhabited τ] [Pure n] [Pure k] : Inhabited (Target α n k τ) :=
  ⟨⟨pure (pure default)⟩⟩

namespace Target

@[inline] def active [Pure n] (target : k (α × τ)) : Target α n k τ :=
  mk <| pure target

@[inline] def nil [NilTrace τ] [Pure n] [Pure k] : Target PUnit n k τ :=
  mk <| pure <| pure <| ((), nilTrace)

@[inline] def activate (self : Target α n k τ) : n (k (α × τ)) :=
  self.task

@[inline] def materializeAsync [Functor n] [Functor k] (self : Target α n k τ) : n (k τ) :=
  ((·.2) <$> ·) <$> self.task

def materialize [Await k m'] [MonadLiftT m' m] [MonadLiftT n m] [Functor m] [Bind m] (self : Target α n k τ) : m τ :=
  liftM self.task >>= fun t => (·.2) <$> liftM (await t)

@[inline] protected def bindSync [BindSync m n k] [Bind n]
(self : Target α n k τ) (f : α → τ → m β) : n (k β) :=
  self.task >>= fun tk => bindSync tk fun (i,t) => f i t

@[inline] protected def bindOpaqueSync
[BindSync m n k] [Bind n] (self : Target α n k τ) (f : τ → m β) : n (k β) :=
  self.task >>= fun tk => bindSync tk fun (_,t) => f t

@[inline] protected def bindAsync
[BindAsync n k] [Bind n] (self : Target α n k τ) (f : α → τ → n (k β)) : n (k β) :=
  self.task >>= fun tk => bindAsync tk fun (i,t) => f i t

@[inline] protected def bindOpaqueAsync
[BindAsync n k] [Bind n] (self : Target α n k τ) (f : τ → n (k β)) : n (k β) :=
  self.task >>= fun tk => bindAsync tk fun (_,t) => f t

def mixOpaqueAsync
[MixTrace τ] [SeqWithAsync n k] [Functor k] [Monad n]
(t1 : Target α n k τ) (t2 :  Target β n k τ) : Target PUnit n k τ := mk do
  let tk1 ← t1.materializeAsync
  let tk2 ← t2.materializeAsync
  ((fun t => ((),t)) <$> ·) <$> seqWithAsync mixTrace tk1 tk2

variable [NilTrace τ] [MixTrace τ]
variable [SeqWithAsync n' k] [Monad n'] [MonadLiftT n' n] [Monad n] [Pure k] [Functor k]

def materializeListAsync (targets : List (Target α n k τ)) : n (k τ) := do
  liftM <| foldRightListAsync mixTrace nilTrace (← targets.mapM (·.materializeAsync))

def materializeArrayAsync (targets : Array (Target α n k τ)) : n (k τ) := do
  liftM <| foldRightArrayAsync mixTrace nilTrace (← targets.mapM (·.materializeAsync))

def collectList (targets : List (Target α n k τ)) : Target (List α) n k τ := mk do
  let tasks ← targets.mapM (·.task)
  let f := fun (i,t') (a,t) => (i :: a, mixTrace t t')
  liftM <| foldLeftListAsync f ([], nilTrace) tasks

def collectArray (targets : Array (Target α n k τ)) : Target (Array α) n k τ := mk do
  let tasks ← targets.mapM (·.task)
  let f := fun (a,t) (i,t') => (a.push i, mixTrace t t')
  liftM <| foldRightArrayAsync f (#[], nilTrace) tasks

def collectOpaqueList (targets : List (Target α n k τ)) : Target PUnit n k τ :=
  mk <| ((fun t => ((), t)) <$> ·) <$> materializeListAsync targets

def collectOpaqueArray (targets : Array (Target α n k τ)) : Target PUnit n k τ :=
  mk <| ((fun t => ((), t)) <$> ·) <$> materializeArrayAsync targets

end Target
