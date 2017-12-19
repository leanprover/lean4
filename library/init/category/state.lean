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

def state_t (σ : Type u) (m : Type u → Type v) [monad m] (α : Type u) : Type (max u v) :=
σ → m (α × σ)

@[reducible] def state (σ α : Type u) : Type u := state_t σ id α

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

  protected def put : σ → state_t σ m punit :=
  λ s' s, return (punit.star, s')

  protected def modify (f : σ → σ) : state_t σ m punit :=
  λ s, return (punit.star, f s)

  protected def embed {α : Type u} (x : state σ α) : state_t σ m α :=
  pure ∘ x

  protected def lift {α : Type u} (t : m α) : state_t σ m α :=
  λ s, do a ← t, return (a, s)

  instance : monad_transformer (state_t σ) :=
  { is_monad := @state_t.monad σ,
    monad_lift := @state_t.lift σ }
end
end state_t

class monad_state (σ : out_param (Type u)) (m : Type u → Type v) [monad m] :=
(embed {} {α : Type u} : state σ α → m α)
(get {} : m σ := embed state_t.get)
(put {} (s : σ) : m punit := embed (state_t.put s))
(embed := λ α x, do p ← x <$> get, put p.2, pure p.1)

export monad_state (get put)

@[inline] def modify {σ : Type u} {m : Type u → Type v} [monad m] [monad_state σ m] (f : σ → σ) :
  m punit := monad_state.embed (state_t.modify f)

instance {σ m} [monad m] : monad_state σ (state_t σ m) :=
{ get := state_t.get, put := state_t.put,
  embed := @state_t.embed _ _ _ }

instance monad_state_lift (s m m') [has_monad_lift m m'] [monad m] [monad_state s m] [monad m'] : monad_state s m' :=
{ get  := monad_lift (get : m _),
  put := monad_lift ∘ (put : _ → m _),
  embed := λ α, monad_lift ∘ (monad_state.embed : _ → m α) }
