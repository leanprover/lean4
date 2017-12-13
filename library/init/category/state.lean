/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import init.meta.interactive
import init.category.id
import init.category.lawful
import init.category.transformers
universes u v

class monad_state (σ : out_param (Type u)) (m : Type u → Type v) [monad m] :=
(state : Π {α : Type u}, (σ → (α × σ)) → m α)
(get : m σ := state (λ s, (s, s)))
(put : σ → m punit := λ s, state (λ _, (punit.star, s)))
-- TODO: `match` in structures
--(state := λ α f, do (a,s) ← f <$> get, put s, pure a)
(state := λ α f, do p ← f <$> get, put p.2, pure p.1)

section
variables {σ : Type u} {m : Type u → Type v} [monad m] [monad_state σ m]
@[inline] def get : m σ := monad_state.get _ _
@[inline] def put' : σ → m punit := monad_state.put _
@[inline] def modify' (f : σ → σ) : m punit := monad_state.state _ (λ s, (punit.star, f s))
end

section
variables {σ : Type} {m : Type → Type v} [monad m] [monad_state σ m]
@[inline] def put : σ → m unit := λ s, put' s $> ()
@[inline] def modify (f : σ → σ) : m unit := modify' f $> ()
end

instance monad_state_lift (s m m') [has_monad_lift m m'] [monad m] [monad_state s m] [monad m'] : monad_state s m' :=
{ get := monad_lift (monad_state.get _ m),
  put := monad_lift ∘ monad_state.put m,
  state := λ α, monad_lift ∘ monad_state.state m }


def state_t (σ : Type u) (m : Type u → Type v) [monad m] (α : Type u) : Type (max u v) :=
σ → m (α × σ)

namespace state_t
section
  variable  {σ : Type u}
  variable  {m : Type u → Type v}
  variable  [monad m]
  variables {α β : Type u}

  protected def return (a : α) : state_t σ m α :=
  λ s, show m (α × σ), from
    return (a, s)

  protected def bind (act₁ : state_t σ m α) (act₂ : α → state_t σ m β) : state_t σ m β :=
  λ s, show m (β × σ), from
     do (a, new_s) ← act₁ s,
        act₂ a new_s

  instance : monad (state_t σ m) :=
  { pure := @state_t.return σ m _, bind := @state_t.bind σ m _ }

  instance (m : Type u → Type v) [lawful_monad m] : lawful_monad (state_t σ m) :=
  {id_map := begin
    intros, funext,
    simp [(<$>), state_t.bind, state_t.return, function.comp, return],
    have h : state_t.bind._match_1 (λ (x : α) (s : σ), @pure m _ _ (x, s)) = pure,
    { funext s, cases s; refl },
    { simp [h, bind_pure] },
  end,
  pure_bind := begin
    intros, funext,
    simp [bind, has_pure.pure, state_t.bind, state_t.return, pure_bind]
  end,
  bind_assoc := begin
    intros, funext,
    simp [bind, state_t.bind, state_t.return, bind_assoc],
    apply congr_arg, funext r,
    cases r, refl
  end, ..state_t.monad}

  protected def orelse [alternative m] (α : Type u) (act₁ act₂ : state_t σ m α) : state_t σ m α :=
  λ s, act₁ s <|> act₂ s

  protected def failure [alternative m] (α : Type u) : state_t σ m α :=
  λ s, failure

  instance [alternative m] : alternative (state_t σ m) :=
  { failure := @state_t.failure σ m _ _,
    orelse  := @state_t.orelse σ m _ _,
    ..state_t.monad }

  protected def get : state_t σ m σ :=
  λ s, return (s, s)

  protected def put : σ → state_t σ m punit :=
  λ s' s, return (punit.star, s')

  protected def state {α : Type u} (f : σ → (α × σ)) : state_t σ m α :=
  pure ∘ f

  protected def lift {α : Type u} (t : m α) : state_t σ m α :=
  λ s, do a ← t, return (a, s)

  instance : monad_state σ (state_t σ m) :=
  { get := state_t.get, put := state_t.put,
    state := @state_t.state _ _ _ }

  instance : monad_transformer (state_t σ) :=
  { is_monad := @state_t.monad σ,
    monad_lift := @state_t.lift σ }
end
end state_t

@[reducible] def state (σ α : Type u) : Type u := state_t σ id α
