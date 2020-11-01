/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich

The State monad transformer.
-/
prelude
import Init.Control.Alternative
import Init.Control.MonadControl
import Init.Control.Id
import Init.Control.Except
universes u v w

def StateT (σ : Type u) (m : Type u → Type v) (α : Type u) : Type (max u v) :=
  σ → m (α × σ)

@[inline] def StateT.run {σ : Type u} {m : Type u → Type v} {α : Type u} (x : StateT σ m α) (s : σ) : m (α × σ) :=
  x s

@[inline] def StateT.run' {σ : Type u} {m : Type u → Type v} [Functor m] {α : Type u} (x : StateT σ m α) (s : σ) : m α :=
  (·.1) <$> x s

@[reducible] def StateM (σ α : Type u) : Type u := StateT σ Id α

instance {σ α} [Subsingleton σ] [Subsingleton α] : Subsingleton (StateM σ α) := ⟨by
  intro x y
  apply funext
  intro s
  match x s, y s with
  | (a₁, s₁), (a₂, s₂) =>
    rw [Subsingleton.elim a₁ a₂, Subsingleton.elim s₁ s₂]
    exact rfl⟩

namespace StateT
section
variables {σ : Type u} {m : Type u → Type v}
variables [Monad m] {α β : Type u}

@[inline] protected def pure (a : α) : StateT σ m α :=
  fun s => pure (a, s)

@[inline] protected def bind (x : StateT σ m α) (f : α → StateT σ m β) : StateT σ m β :=
  fun s => do let (a, s) ← x s; f a s

@[inline] protected def map (f : α → β) (x : StateT σ m α) : StateT σ m β :=
  fun s => do let (a, s) ← x s; pure (f a, s)

instance : Monad (StateT σ m) := {
  pure := StateT.pure,
  bind := StateT.bind,
   map := StateT.map
}

@[inline] protected def orElse [Alternative m] {α : Type u} (x₁ x₂ : StateT σ m α) : StateT σ m α :=
  fun s => x₁ s <|> x₂ s

@[inline] protected def failure [Alternative m] {α : Type u} : StateT σ m α :=
  fun s => failure

instance [Alternative m] : Alternative (StateT σ m) := {
  failure := StateT.failure,
  orElse  := StateT.orElse
}

@[inline] protected def get : StateT σ m σ :=
  fun s => pure (s, s)

@[inline] protected def set : σ → StateT σ m PUnit :=
  fun s' s => pure (⟨⟩, s')

@[inline] protected def modifyGet (f : σ → α × σ) : StateT σ m α :=
  fun s => pure (f s)

@[inline] protected def lift {α : Type u} (t : m α) : StateT σ m α :=
  fun s => do let a ← t; pure (a, s)

instance : MonadLift m (StateT σ m) := ⟨StateT.lift⟩

instance (σ m) [Monad m] : MonadFunctor m (StateT σ m) := ⟨fun f x s => f (x s)⟩

instance (ε) [MonadExceptOf ε m] : MonadExceptOf ε (StateT σ m) := {
  throw    := StateT.lift ∘ throwThe ε,
  tryCatch := fun x c s => tryCatchThe ε (x s) (fun e => c e s)
}

end
end StateT

/-- An implementation of [MonadState](https://hackage.haskell.org/package/mtl-2.2.2/docs/Control-Monad-State-Class.html).
    In contrast to the Haskell implementation, we use overlapping instances to derive instances
    automatically from `monadLift`. -/
class MonadStateOf (σ : Type u) (m : Type u → Type v) :=
  /- Obtain the top-most State of a Monad stack. -/
  (get : m σ)
  /- Set the top-most State of a Monad stack. -/
  (set : σ → m PUnit)
  /- Map the top-most State of a Monad stack.

     Note: `modifyGet f` may be preferable to `do s <- get; let (a, s) := f s; put s; pure a`
     because the latter does not use the State linearly (without sufficient inlining). -/
  (modifyGet {α : Type u} : (σ → α × σ) → m α)

export MonadStateOf (set)

abbrev getThe (σ : Type u) {m : Type u → Type v} [MonadStateOf σ m] : m σ :=
  MonadStateOf.get

@[inline] abbrev modifyThe (σ : Type u) {m : Type u → Type v} [MonadStateOf σ m] (f : σ → σ) : m PUnit :=
  MonadStateOf.modifyGet fun s => (PUnit.unit, f s)

@[inline] abbrev modifyGetThe {α : Type u} (σ : Type u) {m : Type u → Type v} [MonadStateOf σ m] (f : σ → α × σ) : m α :=
  MonadStateOf.modifyGet f

/-- Similar to `MonadStateOf`, but `σ` is an outParam for convenience -/
class MonadState (σ : outParam (Type u)) (m : Type u → Type v) :=
  (get : m σ)
  (set : σ → m PUnit)
  (modifyGet {α : Type u} : (σ → α × σ) → m α)

export MonadState (get modifyGet)

instance (σ : Type u) (m : Type u → Type v) [MonadStateOf σ m] : MonadState σ m := {
  set       := MonadStateOf.set,
  get       := getThe σ,
  modifyGet := fun f => MonadStateOf.modifyGet f
}

section
variables {σ : Type u} {m : Type u → Type v}

@[inline] def modify [MonadState σ m] (f : σ → σ) : m PUnit :=
  modifyGet fun s => (PUnit.unit, f s)

@[inline] def getModify [MonadState σ m] [Monad m] (f : σ → σ) : m σ := do
  modifyGet fun s => (s, f s)

-- NOTE: The Ordering of the following two instances determines that the top-most `StateT` Monad layer
-- will be picked first
instance {n : Type u → Type w} [MonadStateOf σ m] [MonadLift m n] : MonadStateOf σ n := {
  get       := liftM (m := m) MonadStateOf.get,
  set       := fun s => liftM (m := m) $ MonadStateOf.set s,
  modifyGet := fun f => monadLift (m := m) $ MonadState.modifyGet f
}

instance [Monad m] : MonadStateOf σ (StateT σ m) := {
  get       := StateT.get,
  set       := StateT.set,
  modifyGet := StateT.modifyGet
}

end

instance StateT.monadControl (σ : Type u) (m : Type u → Type v) [Monad m] : MonadControl m (StateT σ m) := {
  stM      := fun α   => α × σ,
  liftWith := fun f => do let s ← get; liftM (f (fun x => x.run s)),
  restoreM := fun x => do let (a, s) ← liftM x; set s; pure a
}

instance StateT.tryFinally {m : Type u → Type v} {σ : Type u} [MonadFinally m] [Monad m] : MonadFinally (StateT σ m) := {
  tryFinally' := fun x h s => do
    let ((a, _), (b, s'')) ← tryFinally' (x s) fun
      | some (a, s') => h (some a) s'
      | none         => h none s
    pure ((a, b), s'')
}
