/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich

The continuation monad transformer.
-/

prelude
import init.category.alternative init.category.combinators init.category.lift
universes u v w

structure cont_t (r : Type u) (m : Type u → Type v) (α : Type u) : Type (max u v) :=
(run : (α → m r) → m r)

attribute [pp_using_anonymous_constructor] cont_t

class monad_cont (m : Type u → Type v) :=
(call_cc {α β : Type u} : ((α → m β) → m α) → m α)

@[reducible] def cont (r α : Type u) : Type u := cont_t r id α

namespace cont_t
section
  parameters {r : Type u} {m : Type u → Type v}

  protected def pure {α : Type u} (a : α) : cont_t r m α :=
  ⟨λ cc, cc a⟩

  protected def bind {α β : Type u} (ma : cont_t r m α) (f : α → cont_t r m β) : cont_t r m β :=
  ⟨λ cc, ma.run (λ a, (f a).run cc)⟩

  instance : monad (cont_t r m) :=
  { pure := @pure, bind := @bind }

  protected def call_cc {α β : Type u} (f : ((α → cont_t r m β) → cont_t r m α)) : cont_t r m α :=
  ⟨λ cc, (f (λ a, ⟨λ _, cc a⟩)).run cc⟩

  instance : monad_cont (cont_t r m) :=
  ⟨@call_cc⟩
end
end cont_t
