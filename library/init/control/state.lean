/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich

The State monad transformer.
-/
prelude
import init.control.alternative init.control.lift
import init.control.id init.control.except
universes u v w

def StateT (σ : Type u) (m : Type u → Type v) (α : Type u) : Type (max u v) :=
σ → m (α × σ)

@[inline] def StateT.run {σ : Type u} {m : Type u → Type v} {α : Type u} (x : StateT σ m α) (s : σ) : m (α × σ) :=
x s

@[inline] def StateT.run' {σ : Type u} {m : Type u → Type v} [Functor m] {α : Type u} (x : StateT σ m α) (s : σ) : m α :=
Prod.fst <$> x s

@[reducible] def State (σ α : Type u) : Type u := StateT σ Id α

namespace StateT
section
variables {σ : Type u} {m : Type u → Type v}
variables [Monad m] {α β : Type u}

@[inline] protected def pure (a : α) : StateT σ m α :=
λ s, pure (a, s)

@[inline] protected def bind (x : StateT σ m α) (f : α → StateT σ m β) : StateT σ m β :=
λ s, do (a, s') ← x s, f a s'

instance : Monad (StateT σ m) :=
{ pure := @StateT.pure _ _ _, bind := @StateT.bind _ _ _ }

@[inline] protected def orelse [Alternative m] {α : Type u} (x₁ x₂ : StateT σ m α) : StateT σ m α :=
λ s, x₁ s <|> x₂ s

@[inline] protected def failure [Alternative m] {α : Type u} : StateT σ m α :=
λ s, failure

instance [Alternative m] : Alternative (StateT σ m) :=
{ failure := @StateT.failure _ _ _ _,
  orelse  := @StateT.orelse _ _ _ _,
  .. StateT.Monad }

@[inline] protected def get : StateT σ m σ :=
λ s, pure (s, s)

@[inline] protected def set : σ → StateT σ m PUnit :=
λ s' s, pure (⟨⟩, s')

@[inline] protected def modify (f : σ → σ) : StateT σ m PUnit :=
λ s, pure (⟨⟩, f s)

@[inline] protected def lift {α : Type u} (t : m α) : StateT σ m α :=
λ s, do a ← t, pure (a, s)

instance : HasMonadLift m (StateT σ m) :=
⟨@StateT.lift σ m _⟩

instance (σ m m') [Monad m] [Monad m'] : MonadFunctor m m' (StateT σ m) (StateT σ m') :=
⟨λ _ f x s, f (x s)⟩

@[inline] protected def adapt {σ σ' σ'' α : Type u} {m : Type u → Type v} [Monad m] (split : σ → σ' × σ'')
        (join : σ' → σ'' → σ) (x : StateT σ' m α) : StateT σ m α :=
λ st, do
  let (st, ctx) := split st,
  (a, st') ← x st,
  pure (a, join st' ctx)

instance (ε) [MonadExcept ε m] : MonadExcept ε (StateT σ m) :=
{ throw := λ α, StateT.lift ∘ throw,
  catch := λ α x c s, catch (x s) (λ e, c e s) }
end
end StateT

/-- An implementation of [MonadState](https://hackage.haskell.org/package/mtl-2.2.2/docs/Control-Monad-State-Class.html).
    In contrast to the Haskell implementation, we use overlapping instances to derive instances
    automatically from `monadLift`. -/
class MonadState (σ : outParam (Type u)) (m : Type u → Type v) :=
/- Obtain the top-most State of a Monad stack. -/
(get {} : m σ)
/- Set the top-most State of a Monad stack. -/
(set {} : σ → m PUnit)
/- Map the top-most State of a Monad stack.

   Note: `modify f` may be preferable to `f <$> get >>= put` because the latter
   does not use the State linearly (without sufficient inlining). -/
(modify {} : (σ → σ) → m PUnit)

export MonadState (get set modify)

section
variables {σ : Type u} {m : Type u → Type v}

-- NOTE: The Ordering of the following two instances determines that the top-most `StateT` Monad layer
-- will be picked first
instance monadStateTrans {n : Type u → Type w} [HasMonadLift m n] [MonadState σ m] : MonadState σ n :=
{ get := monadLift (MonadState.get : m _),
  set := λ st, monadLift (MonadState.set st : m _),
  modify := λ f, monadLift (MonadState.modify f : m _) }

instance [Monad m] : MonadState σ (StateT σ m) :=
{ get := StateT.get,
  set := StateT.set,
  modify := StateT.modify }
end

/-- Adapt a Monad stack, changing the Type of its top-most State.

    This class is comparable to [Control.Lens.Zoom](https://hackage.haskell.org/package/lens-4.15.4/docs/Control-Lens-Zoom.html#t:Zoom), but does not use lenses (yet?), and is derived automatically for any transformer implementing `MonadFunctor`.

    For zooming into a part of the State, the `split` Function should split σ into the part σ' and the "context" σ'' so that the potentially modified σ' and the context can be rejoined by `join` in the end.
    In the simplest case, the context can be chosen as the full outer State (ie. `σ'' = σ`), which makes `split` and `join` simpler to define. However, note that the State will not be used linearly in this case.

    Example:
    ```
    def zoomFst {α σ σ' : Type} : State σ α → State (σ × σ') α :=
    adaptState id Prod.mk
    ```

    The Function can also zoom out into a "larger" State, where the new parts are supplied by `split` and discarded by `join` in the end. The State is therefore not used linearly anymore but merely affinely, which is not a practically relevant distinction in Lean.

    Example:
    ```
    def withSnd {α σ σ' : Type} (snd : σ') : State (σ × σ') α → State σ α :=
    adaptState (λ st, ((st, snd), ())) (λ ⟨st,snd⟩ _, st)
    ```

    Note: This class can be seen as a simplification of the more "principled" definition
    ```
    class MonadStateFunctor (σ σ' : outParam (Type u)) (n n' : Type u → Type u) :=
    (map {} {α : Type u} : (∀ {m : Type u → Type u} [Monad m], StateT σ m α → StateT σ' m α) → n α → n' α)
    ```
    which better describes the intent of "we can map a `StateT` anywhere in the Monad stack".
    If we look at the unfolded Type of the first argument `∀ m [Monad m], (σ → m (α × σ)) → σ' → m (α × σ')`, we see that it has the lens Type `∀ f [Functor f], (α → f α) → β → f β` with `f` specialized to `λ σ, m (α × σ)` (exercise: show that this is a lawful Functor). We can build all lenses we are insterested in from the functions `split` and `join` as
    ```
    λ f _ st, let (st, ctx) := split st in
              (λ st', join st' ctx) <$> f st
    ```
    -/
class MonadStateAdapter (σ σ' : outParam (Type u)) (m m' : Type u → Type v) :=
(adaptState {} {σ'' α : Type u} (split : σ' → σ × σ'') (join : σ → σ'' → σ') : m α → m' α)
export MonadStateAdapter (adaptState)

section
variables {σ σ' : Type u} {m m' : Type u → Type v}

def MonadStateAdapter.adaptState' [MonadStateAdapter σ σ' m m'] {α : Type u} (toSigma : σ' → σ) (fromSigma : σ → σ') : m α → m' α :=
adaptState (λ st, (toSigma st, PUnit.unit)) (λ st _, fromSigma st)
export MonadStateAdapter (adaptState')

instance monadStateAdapterTrans {n n' : Type u → Type v} [MonadFunctor m m' n n'] [MonadStateAdapter σ σ' m m'] : MonadStateAdapter σ σ' n n' :=
⟨λ σ'' α split join, monadMap (λ α, (adaptState split join : m α → m' α))⟩

instance [Monad m] : MonadStateAdapter σ σ' (StateT σ m) (StateT σ' m) :=
⟨λ σ'' α, StateT.adapt⟩
end

instance (σ : Type u) (m out : Type u → Type v) [Functor m] [MonadRun out m] : MonadRun (λ α, σ → out α) (StateT σ m) :=
⟨λ α x, run ∘ StateT.run' x⟩

class MonadStateRunner (σ : Type u) (m m' : Type u → Type u) :=
(runState {} {α : Type u} : m α → σ → m' α)
export MonadStateRunner (runState)

section
variables {σ σ' : Type u} {m m' : Type u → Type u}

instance monadStateRunnerTrans {n n' : Type u → Type u} [MonadFunctor m m' n n'] [MonadStateRunner σ m m'] : MonadStateRunner σ n n' :=
⟨λ α x s, monadMap (λ α (y : m α), (runState y s : m' α)) x⟩

instance StateT.MonadStateRunner [Monad m] : MonadStateRunner σ (StateT σ m) m :=
⟨λ α x s, Prod.fst <$> x s⟩
end
