/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich

The continuation monad transformer.
-/

prelude
import init.category.alternative init.category.combinators init.category.lift
universes u v w

structure cont_t (ρ : Type u) (m : Type u → Type v) (α : Type u) : Type (max u v) :=
(run : (α → m ρ) → m ρ)

attribute [pp_using_anonymous_constructor] cont_t

class monad_cont (m : Type u → Type v) :=
(call_cc {α β : Type u} : ((α → m β) → m α) → m α)

@[reducible] def cont (ρ α : Type u) : Type u := cont_t ρ id α

namespace cont_t
section
  parameters {ρ : Type u} {m : Type u → Type v}

  protected def pure {α : Type u} (a : α) : cont_t ρ m α :=
  ⟨λ cc, cc a⟩

  protected def bind {α β : Type u} (ma : cont_t ρ m α) (f : α → cont_t ρ m β) : cont_t ρ m β :=
  ⟨λ cc, ma.run (λ a, (f a).run cc)⟩

  instance : monad (cont_t ρ m) :=
  { pure := @pure, bind := @bind }

  protected def call_cc {α β : Type u} (f : (α → cont_t ρ m β) → cont_t ρ m α) : cont_t ρ m α :=
  ⟨λ cc, (f (λ a, ⟨λ _, cc a⟩)).run cc⟩

  instance : monad_cont (cont_t ρ m) :=
  ⟨@call_cc⟩
end
end cont_t
