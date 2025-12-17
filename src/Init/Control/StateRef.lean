/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich

The State monad transformer using IO references.
-/
module

prelude
public import Init.System.ST

public section

set_option linter.missingDocs true

/--
A state monad that uses an actual mutable reference cell (i.e. an `ST.Ref ω σ`).

The macro `StateRefT σ m α` infers `ω` from `m`. It should normally be used instead.
-/
@[expose] def StateRefT' (ω : Type) (σ : Type) (m : Type → Type) (α : Type) : Type := ReaderT (ST.Ref ω σ) m α

/-! Recall that `StateRefT` is a macro that infers `ω` from the `m`. -/

/--
Executes an action from a monad with added state in the underlying monad `m`. Given an initial
state, it returns a value paired with the final state.

The monad `m` must support `ST` effects in order to create and mutate reference cells.
-/
@[always_inline, inline]
def StateRefT'.run {ω σ : Type} {m : Type → Type} [Monad m] [MonadLiftT (ST ω) m] {α : Type} (x : StateRefT' ω σ m α) (s : σ) : m (α × σ) := do
  let ref ← ST.mkRef s
  let a ← x ref
  let s ← ref.get
  pure (a, s)

/--
Executes an action from a monad with added state in the underlying monad `m`. Given an initial
state, it returns a value, discarding the final state.

The monad `m` must support `ST` effects in order to create and mutate reference cells.
-/
@[always_inline, inline]
def StateRefT'.run' {ω σ : Type} {m : Type → Type} [Monad m] [MonadLiftT (ST ω) m] {α : Type} (x : StateRefT' ω σ m α) (s : σ) : m α := do
  let (a, _) ← x.run s
  pure a

namespace StateRefT'
variable {ω σ : Type} {m : Type → Type} {α : Type}

/--
Runs an action from the underlying monad in the monad with state. The state is not modified.

This function is typically implicitly accessed via a `MonadLiftT` instance as part of [automatic
lifting](lean-manual://section/monad-lifting).
-/
@[always_inline, inline]
protected def lift (x : m α) : StateRefT' ω σ m α :=
  fun _ => x

instance [Monad m] : Monad (StateRefT' ω σ m) := inferInstanceAs (Monad (ReaderT _ _))
instance : MonadLift m (StateRefT' ω σ m) := ⟨StateRefT'.lift⟩
instance (σ m) : MonadFunctor m (StateRefT' ω σ m) := inferInstanceAs (MonadFunctor m (ReaderT _ _))
instance [Alternative m] [Monad m] : Alternative (StateRefT' ω σ m) := inferInstanceAs (Alternative (ReaderT _ _))
instance [Monad m] [MonadAttach m] : MonadAttach (StateRefT' ω σ m) := inferInstanceAs (MonadAttach (ReaderT _ _))

/--
Retrieves the current value of the monad's mutable state.

This increments the reference count of the state, which may inhibit in-place updates.
-/
@[inline]
protected def get [MonadLiftT (ST ω) m] : StateRefT' ω σ m σ :=
  fun ref => ref.get

/--
Replaces the mutable state with a new value.
-/
@[inline]
protected def set [MonadLiftT (ST ω) m] (s : σ) : StateRefT' ω σ m PUnit :=
  fun ref => ref.set s

/--
Applies a function to the current state that both computes a new state and a value. The new state
replaces the current state, and the value is returned.

It is equivalent to a `get` followed by a `set`. However, using `modifyGet` may lead to higher
performance because it doesn't add a new reference to the state value. Additional references can
inhibit in-place updates of data.
-/
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
