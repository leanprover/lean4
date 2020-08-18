/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich

The State monad transformer using IO references.
-/
prelude
import Init.System.IO
import Init.Control.State

def StateRefT (σ : Type) (m : Type → Type) (α : Type) : Type := ReaderT (IO.Ref σ) m α

@[inline] def StateRefT.run {σ : Type} {m : Type → Type} [Monad m] [MonadIO m] {α : Type} (x : StateRefT σ m α) (s : σ) : m (α × σ) := do
ref ← IO.mkRef s;
a ← x ref;
s ← ref.get;
pure (a, s)

@[inline] def StateRefT.run' {σ : Type} {m : Type → Type} [Monad m] [MonadIO m] {α : Type} (x : StateRefT σ m α) (s : σ) : m α := do
(a, _) ← x.run s;
pure a

namespace StateRefT
variables {σ : Type} {m : Type → Type} {α : Type}

@[inline] protected def lift (x : m α) : StateRefT σ m α :=
fun _ => x

instance [Monad m] : Monad (StateRefT σ m) := inferInstanceAs (Monad (ReaderT _ _))
instance [Monad m] [MonadIO m] : MonadIO (StateRefT σ m) := inferInstanceAs (MonadIO (ReaderT _ _))
instance : HasMonadLift m (StateRefT σ m) := ⟨fun _ => StateRefT.lift⟩

@[inline] protected def get [Monad m] [MonadIO m] : StateRefT σ m σ :=
fun ref => ref.get

@[inline] protected def set [Monad m] [MonadIO m] (s : σ) : StateRefT σ m PUnit :=
fun ref => ref.set s

@[inline] protected def modifyGet [Monad m] [MonadIO m] (f : σ → α × σ) : StateRefT σ m α :=
fun ref => ref.modifyGet f

instance [Monad m] [MonadIO m] : MonadState σ (StateRefT σ m) :=
{ get       := StateRefT.get,
  set       := StateRefT.set,
  modifyGet := fun α f => StateRefT.modifyGet f }

instance (ε) [MonadExceptOf ε m] : MonadExceptOf ε (StateRefT σ m) :=
{ throw := fun α => StateRefT.lift ∘ throwThe ε,
  catch := fun α x c s => catchThe ε (x s) (fun e => c e s) }

end StateRefT
