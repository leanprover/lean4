/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import init.category.alternative init.category.transformers
import init.category.id init.category.except
universes u v w

structure state_t (σ : Type u) (m : Type u → Type v) (α : Type u) : Type (max u v) :=
(run' : σ → m (α × σ))

@[reducible] def state (σ α : Type u) : Type u := state_t σ id α

namespace state_t
section
  variable  {σ : Type u}
  variable  {m : Type u → Type v}
  variable  [monad m]
  variables {α β : Type u}

  @[inline] protected def run (st : σ) (x : state_t σ m α) : m (α × σ) :=
  state_t.run' x st

  protected def pure (a : α) : state_t σ m α :=
  ⟨λ s, pure (a, s)⟩

  protected def bind (act₁ : state_t σ m α) (act₂ : α → state_t σ m β) : state_t σ m β :=
  ⟨λ s, do (a, new_s) ← act₁.run s,
           (act₂ a).run new_s⟩

  instance : monad (state_t σ m) :=
  { pure := @state_t.pure σ m _, bind := @state_t.bind σ m _ }

  protected def orelse [alternative m] (α : Type u) (act₁ act₂ : state_t σ m α) : state_t σ m α :=
  ⟨λ s, act₁.run s <|> act₂.run s⟩

  protected def failure [alternative m] (α : Type u) : state_t σ m α :=
  ⟨λ s, failure⟩

  instance [alternative m] : alternative (state_t σ m) :=
  { failure := @state_t.failure σ m _ _,
    orelse  := @state_t.orelse σ m _ _,
    ..state_t.monad }

  protected def get : state_t σ m σ :=
  ⟨λ s, return (s, s)⟩

  protected def put : σ → state_t σ m punit :=
  λ s', ⟨λ s, return (punit.star, s')⟩

  protected def modify (f : σ → σ) : state_t σ m punit :=
  ⟨λ s, return (punit.star, f s)⟩

  protected def lift {α : Type u} (t : m α) : state_t σ m α :=
  ⟨λ s, do a ← t, return (a, s)⟩

  instance (m) [monad m] : has_monad_lift m (state_t σ m) :=
  ⟨@state_t.lift σ m _⟩

  protected def map {σ m m'} [monad m] [monad m'] {α} (f : Π {α}, m α → m' α) : state_t σ m α → state_t σ m' α :=
  λ x, ⟨λ st, f (x.run st)⟩

  instance (σ m m') [monad m] [monad m'] : monad_functor m m' (state_t σ m) (state_t σ m') :=
  ⟨@state_t.map σ m m' _ _⟩

  -- TODO(Sebastian): uses lenses as in https://hackage.haskell.org/package/lens-4.15.4/docs/Control-Lens-Zoom.html#t:Zoom ?
  protected def zoom {σ σ' α : Type u} {m : Type u → Type v} [monad m] (f : σ → σ') (f' : σ' → σ) (x : state_t σ' m α) : state_t σ m α :=
  ⟨λ st, (λ p : α × σ', (p.fst, f' p.snd)) <$> x.run (f st)⟩

  instance (ε) [monad_except ε m] : monad_except ε (state_t σ m) :=
  { throw := λ α, state_t.lift ∘ throw,
    catch := λ α x c, ⟨λ s, catch (x.run s) (state_t.run s ∘ c)⟩ }
end
end state_t

@[reducible] protected def state.run {σ α : Type u} (st : σ) (x : state σ α) : α × σ :=
state_t.run st x

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

class monad_state_functor (σ σ' : out_param (Type u)) (m : out_param (Type u → Type v)) (n n' : Type u → Type w) :=
[functor {} : monad_functor_t (state_t σ m) (state_t σ' m) n n']

attribute [instance] monad_state_functor.mk
local attribute [instance] monad_state_functor.functor

def zoom {σ σ'} {m n n'} [monad m] {α : Type u} (f : σ → σ') (f' : σ' → σ) [monad_state_functor σ' σ m n n'] : n α → n' α :=
monad_map $ λ α, (state_t.zoom f f' : state_t σ' m α → state_t σ m α)

instance (σ m out) [monad_run out m] : monad_run (λ α, σ → out (α × σ)) (state_t σ m) :=
⟨λ α x, run ∘ x.run', λ α a, state_t.mk (unrun ∘ a)⟩
