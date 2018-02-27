/-
Copyright (c) 2016 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich
-/
prelude
import init.function init.coe
import init.category.monad

universes u v w

class has_monad_lift (m : Type u → Type v) (n : Type u → Type w) :=
(monad_lift : ∀ α, m α → n α)

class has_monad_lift_t (m : Type u → Type v) (n : Type u → Type w) :=
(monad_lift {} : ∀ {α}, m α → n α)

export has_monad_lift_t (monad_lift)

@[reducible] def has_monad_lift_to_has_coe {m n} [has_monad_lift_t m n] {α} : has_coe (m α) (n α) :=
⟨monad_lift⟩

instance has_monad_lift_t_trans (m n o) [has_monad_lift n o] [has_monad_lift_t m n] : has_monad_lift_t m o :=
⟨λ α (ma : m α), has_monad_lift.monad_lift o α $ @monad_lift m n _ _ ma⟩

instance has_monad_lift_t_refl (m) : has_monad_lift_t m m :=
⟨λ α, id⟩

@[simp] lemma monad_lift_refl {m : Type u → Type v} {α} : (monad_lift : m α → m α) = id := rfl


/-- A functor in the category of monads. Can be used to lift monad-transforming functions.
    Based on https://hackage.haskell.org/package/pipes-2.4.0/docs/Control-MFunctor.html,
    but not restricted to monad transformers. -/
class monad_functor (m m' : Type u → Type v) (n n' : Type u → Type w) :=
(monad_map {} {α : Type u} : (∀ {α}, m α → m' α) → n α → n' α)

/-- The reflexive-transitive closure of `monad_functor` instances. -/
class monad_functor_t (m m' : Type u → Type v) (n n' : Type u → Type w) :=
(monad_map {} {α : Type u} : (∀ {α}, m α → m' α) → n α → n' α)

export monad_functor_t (monad_map)

def monad_map' {α : Type u} (m m' : Type u → Type v) (n n' : Type u → Type w) [monad_functor_t (λ (α : Type u), m α) (λ (α : Type u), m' punit) n (λ {α : Type u}, n' punit)] : (∀ {α}, m α → m' punit) → n α → n' punit :=
monad_map

instance monad_functor_t_trans (m m' n n' o o') [monad_functor n n' o o'] [monad_functor_t m m' n n'] : monad_functor_t m m' o o' :=
⟨λ α f, monad_functor.monad_map (λ α, (monad_map @f : n α → n' α))⟩

instance monad_functor_t_refl (m m') : monad_functor_t m m' m m' :=
⟨λ α f, f⟩

@[simp] lemma monad_map_refl {m m' : Type u → Type v} (f : ∀ {α}, m α → m' α) {α} : (monad_map @f : m α → m' α) = f := rfl


/-- Run a monad stack to completion. -/
class monad_run (out : out_param $ Type u → Type v) (m : Type u → Type v) :=
(run {} {α : Type u} : m α → out α)
(unrun {} {α : Type u} : out α → m α)

export monad_run (run unrun)
