/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich

The State monad transformer using IO references.
-/
prelude
import Init.System.ST

def StateRefT' (ω : Type) (σ : Type) (m : Type → Type) (α : Type) : Type := ReaderT (ST.Ref ω σ) m α

/-! Recall that `StateRefT` is a macro that infers `ω` from the `m`. -/

@[always_inline, inline]
def StateRefT'.run {ω σ : Type} {m : Type → Type} [Monad m] [MonadLiftT (ST ω) m] {α : Type} (x : StateRefT' ω σ m α) (s : σ) : m (α × σ) := do
  let ref ← ST.mkRef s
  let a ← x ref
  let s ← ref.get
  pure (a, s)

@[always_inline, inline]
def StateRefT'.run' {ω σ : Type} {m : Type → Type} [Monad m] [MonadLiftT (ST ω) m] {α : Type} (x : StateRefT' ω σ m α) (s : σ) : m α := do
  let (a, _) ← x.run s
  pure a

namespace StateRefT'
variable {ω σ : Type} {m : Type → Type} {α : Type}

@[always_inline, inline]
protected def lift (x : m α) : StateRefT' ω σ m α :=
  fun _ => x

instance [Monad m] : Monad (StateRefT' ω σ m) := inferInstanceAs (Monad (ReaderT _ _))
instance : MonadLift m (StateRefT' ω σ m) := ⟨StateRefT'.lift⟩
instance (σ m) : MonadFunctor m (StateRefT' ω σ m) := inferInstanceAs (MonadFunctor m (ReaderT _ _))
instance [Alternative m] [Monad m] : Alternative (StateRefT' ω σ m) := inferInstanceAs (Alternative (ReaderT _ _))

@[inline]
protected def get [MonadLiftT (ST ω) m] : StateRefT' ω σ m σ :=
  fun ref => ref.get

@[inline]
protected def set [MonadLiftT (ST ω) m] (s : σ) : StateRefT' ω σ m PUnit :=
  fun ref => ref.set s

@[inline]
protected def modifyGet [MonadLiftT (ST ω) m] (f : σ → α × σ) : StateRefT' ω σ m α :=
  fun ref => ref.modifyGet f

instance [MonadLiftT (ST ω) m] : MonadStateOf σ (StateRefT' ω σ m) where
  get       := StateRefT'.get
  set       := StateRefT'.set
  modifyGet := StateRefT'.modifyGet

@[always_inline]
instance (ε) [MonadExceptOf ε m] : MonadExceptOf ε (StateRefT' ω σ m) where
  throw    := StateRefT'.lift ∘ throwThe ε
  tryCatch := fun x c s => tryCatchThe ε (x s) (fun e => c e s)

end StateRefT'

instance (ω σ : Type) (m : Type → Type) : MonadControl m (StateRefT' ω σ m) :=
  inferInstanceAs (MonadControl m (ReaderT _ _))

instance {m : Type → Type} {ω σ : Type} [MonadFinally m] : MonadFinally (StateRefT' ω σ m) :=
  inferInstanceAs (MonadFinally (ReaderT _ _))
