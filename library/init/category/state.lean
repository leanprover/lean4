/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import init.category.alternative
import init.category.id
import init.category.transformers
universes u v w

def state_t (σ : Type u) (m : Type u → Type v) (α : Type u) : Type (max u v) :=
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

  instance (m) [monad m] : has_monad_lift m (state_t σ m) :=
  ⟨@state_t.lift σ m _⟩
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


-- TODO(Sebastian): replace with https://hackage.haskell.org/package/lens-4.15.4/docs/Control-Lens-Zoom.html#t:Zoom ?
def with_state_t {σ σ' α : Type u} {m : Type u → Type v} [monad m] (f : σ → σ') : state_t σ' m α → state_t σ m α :=
λ x st, (λ p : α × σ', (p.fst, st)) <$> x (f st)

class monad_state_functor (σ σ' : out_param (Type u)) (m : out_param (Type u → Type v)) (n n' : Type u → Type w) :=
[functor {} : monad_functor_t (state_t σ m) (state_t σ' m) n n']

attribute [instance] monad_state_functor.mk
local attribute [instance] monad_state_functor.functor

def with_state {σ σ'} {m n n'} [monad m] {α : Type u} (f : σ → σ') [monad_state_functor σ' σ m n n'] : n α → n' α :=
monad_map $ λ α, (with_state_t f : state_t σ' m α → state_t σ m α)

def map_state_t {σ m m'} [monad m] [monad m'] {α} (f : Π {α}, m α → m' α) : state_t σ m α → state_t σ m' α :=
λ x st, f (x st)

instance (σ m m') [monad m] [monad m'] : monad_functor m m' (state_t σ m) (state_t σ m') :=
⟨@map_state_t σ m m' _ _⟩
