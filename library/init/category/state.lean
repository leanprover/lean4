/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich

The state monad transformer.
-/
prelude
import init.category.alternative init.category.lift
import init.category.id init.category.except
universes u v w

structure state_t (σ : Type u) (m : Type u → Type v) (α : Type u) : Type (max u v) :=
(run : σ → m (α × σ))

attribute [pp_using_anonymous_constructor] state_t

@[reducible] def state (σ α : Type u) : Type u := state_t σ id α

namespace state_t
section
  variables {σ : Type u} {m : Type u → Type v}

  variable  [monad m]
  variables {α β : Type u}

  @[inline] protected def pure (a : α) : state_t σ m α :=
  ⟨λ s, pure (a, s)⟩

  @[inline] protected def bind (x : state_t σ m α) (f : α → state_t σ m β) : state_t σ m β :=
  ⟨λ s, do (a, s') ← x.run s,
           (f a).run s'⟩

  instance : monad (state_t σ m) :=
  { pure := @state_t.pure _ _ _, bind := @state_t.bind _ _ _ }

  protected def orelse [alternative m] {α : Type u} (x₁ x₂ : state_t σ m α) : state_t σ m α :=
  ⟨λ s, x₁.run s <|> x₂.run s⟩

  protected def failure [alternative m] {α : Type u} : state_t σ m α :=
  ⟨λ s, failure⟩

  instance [alternative m] : alternative (state_t σ m) :=
  { failure := @state_t.failure _ _ _ _,
    orelse  := @state_t.orelse _ _ _ _ }

  @[inline] protected def get : state_t σ m σ :=
  ⟨λ s, pure (s, s)⟩

  @[inline] protected def put : σ → state_t σ m punit :=
  λ s', ⟨λ s, pure (punit.star, s')⟩

  @[inline] protected def modify (f : σ → σ) : state_t σ m punit :=
  ⟨λ s, pure (punit.star, f s)⟩

  @[inline] protected def lift {α : Type u} (t : m α) : state_t σ m α :=
  ⟨λ s, do a ← t, pure (a, s)⟩

  instance : has_monad_lift m (state_t σ m) :=
  ⟨@state_t.lift σ m _⟩

  @[inline] protected def monad_map {σ m m'} [monad m] [monad m'] {α} (f : Π {α}, m α → m' α) :
    state_t σ m α → state_t σ m' α :=
  λ x, ⟨λ st, f (x.run st)⟩

  instance (σ m m') [monad m] [monad m'] : monad_functor m m' (state_t σ m) (state_t σ m') :=
  ⟨@state_t.monad_map σ m m' _ _⟩

  protected def zoom {σ σ' σ'' α : Type u} {m : Type u → Type v} [monad m] (split : σ → σ' × σ'')
    (join : σ' → σ'' → σ) (x : state_t σ' m α) : state_t σ m α :=
  ⟨λ st, do let (st, ctx) := split st,
            (a, st') ← x.run st,
            pure (a, join st' ctx)⟩

  instance (ε) [monad_except ε m] : monad_except ε (state_t σ m) :=
  { throw := λ α, state_t.lift ∘ throw,
    catch := λ α x c, ⟨λ s, catch (x.run s) (λ e, state_t.run (c e) s)⟩ }
end
end state_t

/-- A specialization of `monad_lift` to lifting `state_t` that allows `σ` to be inferred.

    This class is roughly equivalent to `MonadState` from https://hackage.haskell.org/package/mtl-2.2.2/docs/Control-Monad-State-Class.html,
    with the important distinction that it is automatically derived via the generic
    `has_monad_lift` class. -/
class monad_state_lift (σ : out_param (Type u)) (m : out_param (Type u → Type v)) (n : Type u → Type w) :=
[has_lift : has_monad_lift_t (state_t σ m) n]

attribute [instance] monad_state_lift.mk
local attribute [instance] monad_state_lift.has_lift

section
variables {σ : Type u} {m : Type u → Type v} {n : Type u → Type w} [monad m] [monad_state_lift σ m n]

/-- Obtain the top-most state of a monad stack. -/
@[inline] def get : n σ :=
@monad_lift _ _ _ _ (state_t.get : state_t σ m _)

/-- Set the top-most state of a monad stack. -/
@[inline] def put (st : σ) : n punit :=
monad_lift (state_t.put st : state_t σ m _)

/-- Map the top-most state of a monad stack.

    Note: `modify f` may be preferable to `f <$> get >>= put` because the latter
    does not use the state linearly (without sufficient inlining). -/
@[inline] def modify (f : σ → σ) : n punit :=
monad_lift (state_t.modify f : state_t σ m _)
end

/-- Get the state at a specific position in the monad stack.

    Example: <first figure out if this is the correct way to go> -/
@[inline] def get_type (m : Type u → Type v) {n : Type u → Type w} (σ : Type u) [has_monad_lift_t (state_t σ m) n] [monad m] : n σ :=
get


/-- A specialization of `monad_map` to `state_t` that allows `σ` to be inferred. -/
class monad_state_functor (σ σ' : out_param (Type u)) (m : out_param (Type u → Type v)) (n n' : Type u → Type w) :=
[functor {} : monad_functor_t (state_t σ m) (state_t σ' m) n n']

attribute [instance] monad_state_functor.mk
local attribute [instance] monad_state_functor.functor

/-- Change the top-most state type of a monad stack.
    This allows zooming into a part of the state.
    The `split` function should split σ into the part σ' and the "context" σ'' so
    that the potentially modified σ' and the context can be rejoined by `join`
    in the end.
    In the simplest case, the context can be chosen as the full outer state
    (ie. `σ'' = σ`), which makes `split` and `join` simpler to define. However,
    note that the state will not be used linearly in this case.

    Example:
    ```
    def zoom_fst {α σ σ' : Type} : state σ α → state (σ × σ') α :=
    zoom id prod.mk
    ```
    -/
-- TODO(Sebastian): replace with proper lenses
def zoom {σ σ' σ''} {m n n'} [monad_state_functor σ' σ m n n'] [monad m] {α : Type u} (split : σ → σ' × σ'') (join : σ' → σ'' → σ)
  : n α → n' α :=
monad_map $ λ α, (state_t.zoom split join : state_t σ' m α → state_t σ m α)


instance (σ m out) [monad_run out m] : monad_run (λ α, σ → out (α × σ)) (state_t σ m) :=
⟨λ α x, run ∘ (λ σ, x.run σ), λ α a, state_t.mk (unrun ∘ a)⟩
