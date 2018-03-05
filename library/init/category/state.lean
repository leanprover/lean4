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

  -- TODO(Sebastian): uses lenses as in https://hackage.haskell.org/package/lens-4.15.4/docs/Control-Lens-Zoom.html#t:Zoom ?
  protected def zoom {σ σ' α : Type u} {m : Type u → Type v} [monad m] (get : σ → σ')
    (set : σ' → σ → σ) (x : state_t σ' m α) : state_t σ m α :=
  ⟨λ st, do (a, st') ← x.run (get st),
            pure (a, set st' st)⟩

  instance (ε) [monad_except ε m] : monad_except ε (state_t σ m) :=
  { throw := λ α, state_t.lift ∘ throw,
    catch := λ α x c, ⟨λ s, catch (x.run s) (λ e, state_t.run (c e) s)⟩ }
end
end state_t

/-- A specialization of `monad_lift` to `state_t` that allows `σ` to be inferred. -/
class monad_state_lift (σ : out_param (Type u)) (m : out_param (Type u → Type v)) (n : Type u → Type w) :=
[has_lift : has_monad_lift_t (state_t σ m) n]

attribute [instance] monad_state_lift.mk
local attribute [instance] monad_state_lift.has_lift

section
variables {σ : Type u} {m : Type u → Type v} {n : Type u → Type w} [monad m] [monad_state_lift σ m n]

@[inline] def get : n σ :=
@monad_lift _ _ _ _ (state_t.get : state_t σ m _)

@[inline] def get_type (σ : Type u) [has_monad_lift_t (state_t σ m) n] : n σ :=
get

@[inline] def put (st : σ) : n punit :=
monad_lift (state_t.put st : state_t σ m _)

@[inline] def modify (f : σ → σ) : n punit :=
monad_lift (state_t.modify f : state_t σ m _)
end


/-- A specialization of `monad_map` to `state_t` that allows `σ` to be inferred. -/
class monad_state_functor (σ σ' : out_param (Type u)) (m : out_param (Type u → Type v)) (n n' : Type u → Type w) :=
[functor {} : monad_functor_t (state_t σ m) (state_t σ' m) n n']

attribute [instance] monad_state_functor.mk
local attribute [instance] monad_state_functor.functor

def zoom {σ σ'} {m n n'} [monad m] {α : Type u} (get : σ → σ') (set : σ' → σ → σ)
  [monad_state_functor σ' σ m n n'] : n α → n' α :=
monad_map $ λ α, (state_t.zoom get set : state_t σ' m α → state_t σ m α)

instance (σ m out) [monad_run out m] : monad_run (λ α, σ → out (α × σ)) (state_t σ m) :=
⟨λ α x, run ∘ (λ σ, x.run σ), λ α a, state_t.mk (unrun ∘ a)⟩
