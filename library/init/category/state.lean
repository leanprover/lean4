/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import init.category.alternative
import init.category.id
import init.category.transformers
universes u v

class monad_state (σ : out_param (Type u)) (m : Type u → Type v) [monad m] :=
(state {} {α : Type u} : (σ → (α × σ)) → m α)
(get {} : m σ := state (λ s, (s, s)))
(put' {} (s : σ) : m punit := state (λ _, (punit.star, s)))
(state := λ α f, do p ← f <$> get, put' p.2, pure p.1)

export monad_state (get put')

@[inline] def modify' {σ : Type u} {m : Type u → Type v} [monad m] [monad_state σ m] (f : σ → σ) :
  m punit := monad_state.state (λ s, (punit.star, f s))

section
variables {σ : Type} {m : Type → Type v} [monad m] [monad_state σ m]
@[inline] def put : σ → m unit := λ s, put' s $> ()
@[inline] def modify (f : σ → σ) : m unit := modify' f $> ()
end

instance monad_state_lift (s m m') [has_monad_lift m m'] [monad m] [monad_state s m] [monad m'] : monad_state s m' :=
{ get  := monad_lift (@get _ m _ _),
  put' := monad_lift ∘ @put' _ m _ _,
  state := λ α, monad_lift ∘ @monad_state.state _ m _ _ _ }


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

  protected def put' : σ → state_t σ m punit :=
  λ s' s, return (punit.star, s')

  protected def state {α : Type u} (f : σ → (α × σ)) : state_t σ m α :=
  pure ∘ f

  protected def lift {α : Type u} (t : m α) : state_t σ m α :=
  λ s, do a ← t, return (a, s)

  instance : monad_state σ (state_t σ m) :=
  { get := state_t.get, put' := state_t.put',
    state := @state_t.state _ _ _ }

  instance : monad_transformer (state_t σ) :=
  { is_monad := @state_t.monad σ,
    monad_lift := @state_t.lift σ }
end
end state_t

@[reducible] def state (σ α : Type u) : Type u := state_t σ id α
