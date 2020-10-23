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
Prod.fst <$> x s

@[reducible] def StateM (σ α : Type u) : Type u := StateT σ Id α

instance StateM.subsingleton {σ α} [Subsingleton σ] [Subsingleton α] : Subsingleton (StateM σ α) :=
⟨λ x y => funext $ fun (s : σ) => match x s, y s with
  | (a₁, s₁), (a₂, s₂) => Subsingleton.elim a₁ a₂ ▸ Subsingleton.elim s₁ s₂ ▸ rfl⟩

namespace StateT
section
variables {σ : Type u} {m : Type u → Type v}
variables [Monad m] {α β : Type u}

@[inline] protected def pure (a : α) : StateT σ m α :=
fun s => pure (a, s)

@[inline] protected def bind (x : StateT σ m α) (f : α → StateT σ m β) : StateT σ m β :=
fun s => do (a, s) ← x s; f a s

@[inline] protected def map (f : α → β) (x : StateT σ m α) : StateT σ m β :=
fun s => do (a, s) ← x s; pure (f a, s)

instance : Monad (StateT σ m) :=
{ pure := @StateT.pure _ _ _, bind := @StateT.bind _ _ _, map := @StateT.map _ _ _ }

@[inline] protected def orelse [Alternative m] {α : Type u} (x₁ x₂ : StateT σ m α) : StateT σ m α :=
fun s => x₁ s <|> x₂ s

@[inline] protected def failure [Alternative m] {α : Type u} : StateT σ m α :=
fun s => failure

instance [Alternative m] : Alternative (StateT σ m) :=
{ StateT.Monad with
  failure := @StateT.failure _ _ _ _,
  orelse  := @StateT.orelse _ _ _ _ }

@[inline] protected def get : StateT σ m σ :=
fun s => pure (s, s)

@[inline] protected def set : σ → StateT σ m PUnit :=
fun s' s => pure (⟨⟩, s')

@[inline] protected def modifyGet (f : σ → α × σ) : StateT σ m α :=
fun s => pure (f s)

@[inline] protected def lift {α : Type u} (t : m α) : StateT σ m α :=
fun s => do a ← t; pure (a, s)

instance : MonadLift m (StateT σ m) :=
⟨@StateT.lift σ m _⟩

instance (σ m) [Monad m] : MonadFunctor m (StateT σ m) :=
⟨fun _ f x s => f (x s)⟩

@[inline] protected def adapt {σ σ' σ'' α : Type u} {m : Type u → Type v} [Monad m] (split : σ → σ' × σ'')
        (join : σ' → σ'' → σ) (x : StateT σ' m α) : StateT σ m α :=
fun st => do
  let (st, ctx) := split st;
  (a, st') ← x st;
  pure (a, join st' ctx)

instance (ε) [MonadExceptOf ε m] : MonadExceptOf ε (StateT σ m) :=
{ throw := fun α => StateT.lift ∘ throwThe ε,
  tryCatch := fun α x c s => tryCatchThe ε (x s) (fun e => c e s) }

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

instance monadStateOf.isMonadState (σ : Type u) (m : Type u → Type v) [MonadStateOf σ m] : MonadState σ m :=
{ set       := MonadStateOf.set,
  get       := getThe σ,
  modifyGet := fun α f => MonadStateOf.modifyGet f }

section
variables {σ : Type u} {m : Type u → Type v}

@[inline] def modify [MonadState σ m] (f : σ → σ) : m PUnit :=
modifyGet fun s => (PUnit.unit, f s)

@[inline] def getModify [MonadState σ m] [Monad m] (f : σ → σ) : m σ := do
modifyGet fun s => (s, f s)

-- NOTE: The Ordering of the following two instances determines that the top-most `StateT` Monad layer
-- will be picked first
instance monadStateTrans {n : Type u → Type w} [MonadStateOf σ m] [MonadLift m n] : MonadStateOf σ n :=
{ get       := monadLift (MonadStateOf.get : m _),
  set       := fun st => monadLift (MonadStateOf.set st : m _),
  modifyGet := fun α f => monadLift (MonadState.modifyGet f : m _) }

instance [Monad m] : MonadStateOf σ (StateT σ m) :=
{ get := StateT.get,
  set := StateT.set,
  modifyGet := @StateT.modifyGet _ _ _ }

end

instance StateT.monadControl (σ : Type u) (m : Type u → Type v) [Monad m] : MonadControl m (StateT σ m) := {
  stM      := fun α   => α × σ,
  liftWith := fun α f => do s ← get; liftM (f (fun β x => x.run s)),
  restoreM := fun α x => do (a, s) ← liftM x; set s; pure a
}

instance StateT.tryFinally {m : Type u → Type v} {σ : Type u} [MonadFinally m] [Monad m] : MonadFinally (StateT σ m) :=
{ tryFinally' := fun α β x h s => do
  ((a, _), (b, s'')) ← tryFinally' (x s)
    (fun p? => match p? with
      | some (a, s') => h (some a) s'
      | none         => h none s);
  pure ((a, b), s'') }
