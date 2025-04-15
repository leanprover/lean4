/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich

The State monad transformer.
-/
prelude
import Init.Control.Basic
import Init.Control.Id
import Init.Control.Except

set_option linter.missingDocs true

universe u v w

/--
Adds a mutable state of type `σ` to a monad.

Actions in the resulting monad are functions that take an initial state and return, in `m`, a tuple
of a value and a state.
-/
def StateT (σ : Type u) (m : Type u → Type v) (α : Type u) : Type (max u v) :=
  σ → m (α × σ)

/--
Executes an action from a monad with added state in the underlying monad `m`. Given an initial
state, it returns a value paired with the final state.
-/
@[always_inline, inline]
def StateT.run {σ : Type u} {m : Type u → Type v} {α : Type u} (x : StateT σ m α) (s : σ) : m (α × σ) :=
  x s

/--
Executes an action from a monad with added state in the underlying monad `m`. Given an initial
state, it returns a value, discarding the final state.
-/
@[always_inline, inline]
def StateT.run' {σ : Type u} {m : Type u → Type v} [Functor m] {α : Type u} (x : StateT σ m α) (s : σ) : m α :=
  (·.1) <$> x s

/--
A tuple-based state monad.

Actions in `StateM σ` are functions that take an initial state and return a value paired with a
final state.
-/
@[reducible]
def StateM (σ α : Type u) : Type u := StateT σ Id α

instance {σ α} [Subsingleton σ] [Subsingleton α] : Subsingleton (StateM σ α) where
  allEq x y := by
    apply funext
    intro s
    match x s, y s with
    | (a₁, s₁), (a₂, s₂) =>
      rw [Subsingleton.elim a₁ a₂, Subsingleton.elim s₁ s₂]

namespace StateT
section
variable {σ : Type u} {m : Type u → Type v}
variable [Monad m] {α β : Type u}

/--
Returns the given value without modifying the state. Typically used via `Pure.pure`.
-/
@[always_inline, inline]
protected def pure (a : α) : StateT σ m α :=
  fun s => pure (a, s)

/--
Sequences two actions. Typically used via the `>>=` operator.
-/
@[always_inline, inline]
protected def bind (x : StateT σ m α) (f : α → StateT σ m β) : StateT σ m β :=
  fun s => do let (a, s) ← x s; f a s

/--
Modifies the value returned by a computation. Typically used via the `<$>` operator.
-/
@[always_inline, inline]
protected def map (f : α → β) (x : StateT σ m α) : StateT σ m β :=
  fun s => do let (a, s) ← x s; pure (f a, s)

@[always_inline]
instance : Monad (StateT σ m) where
  pure := StateT.pure
  bind := StateT.bind
  map  := StateT.map

/--
Recovers from errors. The state is rolled back on error recovery. Typically used via the `<|>`
operator.
-/
@[always_inline, inline]
protected def orElse [Alternative m] {α : Type u} (x₁ : StateT σ m α) (x₂ : Unit → StateT σ m α) : StateT σ m α :=
  fun s => x₁ s <|> x₂ () s

/--
Fails with a recoverable error. The state is rolled back on error recovery.
-/
@[always_inline, inline]
protected def failure [Alternative m] {α : Type u} : StateT σ m α :=
  fun _ => failure

instance [Alternative m] : Alternative (StateT σ m) where
  failure := StateT.failure
  orElse  := StateT.orElse

/--
Retrieves the current value of the monad's mutable state.

This increments the reference count of the state, which may inhibit in-place updates.
-/
@[always_inline, inline]
protected def get : StateT σ m σ :=
  fun s => pure (s, s)

/--
Replaces the mutable state with a new value.
-/
@[always_inline, inline]
protected def set : σ → StateT σ m PUnit :=
  fun s' _ => pure (⟨⟩, s')

/--
Applies a function to the current state that both computes a new state and a value. The new state
replaces the current state, and the value is returned.

It is equivalent to `do let (a, s) := f (← StateT.get); StateT.set s; pure a`. However, using
`StateT.modifyGet` may lead to better performance because it doesn't add a new reference to the
state value, and additional references can inhibit in-place updates of data.
-/
@[always_inline, inline]
protected def modifyGet (f : σ → α × σ) : StateT σ m α :=
  fun s => pure (f s)

/--
Runs an action from the underlying monad in the monad with state. The state is not modified.

This function is typically implicitly accessed via a `MonadLiftT` instance as part of [automatic
lifting](lean-manual://section/monad-lifting).
-/
@[always_inline, inline]
protected def lift {α : Type u} (t : m α) : StateT σ m α :=
  fun s => do let a ← t; pure (a, s)

instance : MonadLift m (StateT σ m) := ⟨StateT.lift⟩

@[always_inline]
instance (σ m) : MonadFunctor m (StateT σ m) := ⟨fun f x s => f (x s)⟩

@[always_inline]
instance (ε) [MonadExceptOf ε m] : MonadExceptOf ε (StateT σ m) := {
  throw    := StateT.lift ∘ throwThe ε
  tryCatch := fun x c s => tryCatchThe ε (x s) (fun e => c e s)
}

end
end StateT

/--
Creates a suitable implementation of `ForIn.forIn` from a `ForM` instance.
-/
@[always_inline, inline]
def ForM.forIn [Monad m] [ForM (StateT β (ExceptT β m)) ρ α]
    (x : ρ) (b : β) (f : α → β → m (ForInStep β)) : m β := do
  let g a b := .mk do
    match ← f a b with
    | .yield b' => pure (.ok (⟨⟩, b'))
    | .done b' => pure (.error b')
  match ← forM (m := StateT β (ExceptT β m)) (α := α) x g |>.run b |>.run with
  | .ok a => pure a.2
  | .error a => pure a

section
variable {σ : Type u} {m : Type u → Type v}

instance [Monad m] : MonadStateOf σ (StateT σ m) where
  get       := StateT.get
  set       := StateT.set
  modifyGet := StateT.modifyGet

end

@[always_inline]
instance StateT.monadControl (σ : Type u) (m : Type u → Type v) [Monad m] : MonadControl m (StateT σ m) where
  stM      := fun α   => α × σ
  liftWith := fun f => do let s ← get; liftM (f (fun x => x.run s))
  restoreM := fun x => do let (a, s) ← liftM x; set s; pure a

@[always_inline]
instance StateT.tryFinally {m : Type u → Type v} {σ : Type u} [MonadFinally m] [Monad m] : MonadFinally (StateT σ m) where
  tryFinally' := fun x h s => do
    let ((a, _), (b, s'')) ← tryFinally' (x s) fun
      | some (a, s') => h (some a) s'
      | none         => h none s
    pure ((a, b), s'')
