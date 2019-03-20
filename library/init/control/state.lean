/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich

The state monad transformer.
-/
prelude
import init.control.alternative init.control.lift
import init.control.id init.control.except
universes u v w

def stateT (σ : Type u) (m : Type u → Type v) (α : Type u) : Type (max u v) :=
σ → m (α × σ)

@[inline] def stateT.run {σ : Type u} {m : Type u → Type v} {α : Type u} (x : stateT σ m α) (s : σ) : m (α × σ) :=
x s

@[inline] def stateT.run' {σ : Type u} {m : Type u → Type v} [functor m] {α : Type u} (x : stateT σ m α) (s : σ) : m α :=
prod.fst <$> x s

@[reducible] def state (σ α : Type u) : Type u := stateT σ id α

namespace stateT
section
  variables {σ : Type u} {m : Type u → Type v}

  variable  [monad m]
  variables {α β : Type u}

  @[inline] protected def pure (a : α) : stateT σ m α :=
  λ s, pure (a, s)

  @[inline] protected def bind (x : stateT σ m α) (f : α → stateT σ m β) : stateT σ m β :=
  λ s, do (a, s') ← x s,
          f a s'

  instance : monad (stateT σ m) :=
  { pure := @stateT.pure _ _ _, bind := @stateT.bind _ _ _ }

  @[inline] protected def orelse [alternative m] {α : Type u} (x₁ x₂ : stateT σ m α) : stateT σ m α :=
  λ s, x₁ s <|> x₂ s

  @[inline] protected def failure [alternative m] {α : Type u} : stateT σ m α :=
  λ s, failure

  instance [alternative m] : alternative (stateT σ m) :=
  { failure := @stateT.failure _ _ _ _,
    orelse  := @stateT.orelse _ _ _ _,
    ..stateT.monad }

  @[inline] protected def get : stateT σ m σ :=
  λ s, pure (s, s)

  @[inline] protected def put : σ → stateT σ m punit :=
  λ s' s, pure (punit.star, s')

  @[inline] protected def modify (f : σ → σ) : stateT σ m punit :=
  λ s, pure (punit.star, f s)

  @[inline] protected def lift {α : Type u} (t : m α) : stateT σ m α :=
  λ s, do a ← t, pure (a, s)

  instance : hasMonadLift m (stateT σ m) :=
  ⟨@stateT.lift σ m _⟩

  instance (σ m m') [monad m] [monad m'] : monadFunctor m m' (stateT σ m) (stateT σ m') :=
  ⟨λ _ f x s, f (x s)⟩

  @[inline] protected def adapt {σ σ' σ'' α : Type u} {m : Type u → Type v} [monad m] (split : σ → σ' × σ'')
    (join : σ' → σ'' → σ) (x : stateT σ' m α) : stateT σ m α :=
  λ st, do let (st, ctx) := split st,
           (a, st') ← x st,
           pure (a, join st' ctx)

  instance (ε) [monadExcept ε m] : monadExcept ε (stateT σ m) :=
  { throw := λ α, stateT.lift ∘ throw,
    catch := λ α x c s, catch (x s) (λ e, c e s) }
end
end stateT

/-- An implementation of [MonadState](https://hackage.haskell.org/package/mtl-2.2.2/docs/Control-Monad-State-Class.html).
    In contrast to the Haskell implementation, we use overlapping instances to derive instances
    automatically from `monadLift`. -/
class monadState (σ : outParam (Type u)) (m : Type u → Type v) :=
/- Obtain the top-most state of a monad stack. -/
(get {} : m σ)
/- Set the top-most state of a monad stack. -/
(put {} : σ → m punit)
/- Map the top-most state of a monad stack.

   Note: `modify f` may be preferable to `f <$> get >>= put` because the latter
   does not use the state linearly (without sufficient inlining). -/
(modify {} : (σ → σ) → m punit)

export monadState (get put modify)

section
variables {σ : Type u} {m : Type u → Type v}

-- NOTE: The ordering of the following two instances determines that the top-most `stateT` monad layer
-- will be picked first
instance monadStateTrans {n : Type u → Type w} [hasMonadLift m n] [monadState σ m] : monadState σ n :=
{ get := monadLift (monadState.get : m _),
  put := λ st, monadLift (monadState.put st : m _),
  modify := λ f, monadLift (monadState.modify f : m _) }

instance [monad m] : monadState σ (stateT σ m) :=
{ get := stateT.get,
  put := stateT.put,
  modify := stateT.modify }
end

/-- Adapt a monad stack, changing the type of its top-most state.

    This class is comparable to [Control.Lens.Zoom](https://hackage.haskell.org/package/lens-4.15.4/docs/Control-Lens-Zoom.html#t:Zoom), but does not use lenses (yet?), and is derived automatically for any transformer implementing `monadFunctor`.

    For zooming into a part of the state, the `split` function should split σ into the part σ' and the "context" σ'' so that the potentially modified σ' and the context can be rejoined by `join` in the end.
    In the simplest case, the context can be chosen as the full outer state (ie. `σ'' = σ`), which makes `split` and `join` simpler to define. However, note that the state will not be used linearly in this case.

    Example:
    ```
    def zoomFst {α σ σ' : Type} : state σ α → state (σ × σ') α :=
    adaptState id prod.mk
    ```

    The function can also zoom out into a "larger" state, where the new parts are supplied by `split` and discarded by `join` in the end. The state is therefore not used linearly anymore but merely affinely, which is not a practically relevant distinction in Lean.

    Example:
    ```
    def withSnd {α σ σ' : Type} (snd : σ') : state (σ × σ') α → state σ α :=
    adaptState (λ st, ((st, snd), ())) (λ ⟨st,snd⟩ _, st)
    ```

    Note: This class can be seen as a simplification of the more "principled" definition
    ```
    class monadStateFunctor (σ σ' : outParam (Type u)) (n n' : Type u → Type u) :=
    (map {} {α : Type u} : (∀ {m : Type u → Type u} [monad m], stateT σ m α → stateT σ' m α) → n α → n' α)
    ```
    which better describes the intent of "we can map a `stateT` anywhere in the monad stack".
    If we look at the unfolded type of the first argument `∀ m [monad m], (σ → m (α × σ)) → σ' → m (α × σ')`, we see that it has the lens type `∀ f [functor f], (α → f α) → β → f β` with `f` specialized to `λ σ, m (α × σ)` (exercise: show that this is a lawful functor). We can build all lenses we are insterested in from the functions `split` and `join` as
    ```
    λ f _ st, let (st, ctx) := split st in
              (λ st', join st' ctx) <$> f st
    ```
    -/
class monadStateAdapter (σ σ' : outParam (Type u)) (m m' : Type u → Type v) :=
(adaptState {} {σ'' α : Type u} (split : σ' → σ × σ'') (join : σ → σ'' → σ') : m α → m' α)
export monadStateAdapter (adaptState)

section
variables {σ σ' : Type u} {m m' : Type u → Type v}

def monadStateAdapter.adaptState' [monadStateAdapter σ σ' m m'] {α : Type u} (toΣ : σ' → σ) (fromΣ : σ → σ') : m α → m' α :=
adaptState (λ st, (toΣ st, punit.star)) (λ st _, fromΣ st)
export monadStateAdapter (adaptState')

instance monadStateAdapterTrans {n n' : Type u → Type v} [monadFunctor m m' n n'] [monadStateAdapter σ σ' m m'] : monadStateAdapter σ σ' n n' :=
⟨λ σ'' α split join, monadMap (λ α, (adaptState split join : m α → m' α))⟩

instance [monad m] : monadStateAdapter σ σ' (stateT σ m) (stateT σ' m) :=
⟨λ σ'' α, stateT.adapt⟩
end

instance (σ : Type u) (m out : Type u → Type v) [functor m] [monadRun out m] : monadRun (λ α, σ → out α) (stateT σ m) :=
⟨λ α x, run ∘ stateT.run' x⟩

class monadStateRunner (σ : Type u) (m m' : Type u → Type u) :=
(runState {} {α : Type u} : m α → σ → m' α)
export monadStateRunner (runState)

section
variables {σ σ' : Type u} {m m' : Type u → Type u}

instance monadStateRunnerTrans {n n' : Type u → Type u} [monadFunctor m m' n n'] [monadStateRunner σ m m'] : monadStateRunner σ n n' :=
⟨λ α x s, monadMap (λ α (y : m α), (runState y s : m' α)) x⟩

instance stateT.monadStateRunner [monad m] : monadStateRunner σ (stateT σ m) m :=
⟨λ α x s, prod.fst <$> x s⟩
end
