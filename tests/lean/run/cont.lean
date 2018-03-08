/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich

The continuation monad transformer.
-/

import init.category.alternative init.category.combinators init.category.lift
import system.io
universes u v w

/-- An implementation of [ContT](https://hackage.haskell.org/package/mtl-2.2.2/docs/Control-Monad-Cont.html#t:ContT) -/
structure cont_t (ρ : Type u) (m : Type u → Type v) (α : Type u) : Type (max u v) :=
(run : (α → m ρ) → m ρ)

attribute [pp_using_anonymous_constructor] cont_t

/-- An implementation of [MonadCont done right](https://wiki.haskell.org/MonadCont_done_right) -/
class monad_cont (m : Type u → Type v) :=
/- Call a function with the current continuation (cc) as its argument, which can be called to
   exit the function from anywhere inside it. -/
(call_cc {α : Type u} : ((∀ {β}, α → m β) → m α) → m α)

export monad_cont (call_cc)

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

  protected def call_cc {α : Type u} (f : (∀ {β}, α → cont_t ρ m β) → cont_t ρ m α) : cont_t ρ m α :=
  ⟨λ cc, (f (λ _ a, ⟨λ _, cc a⟩)).run cc⟩

  instance : monad_cont (cont_t ρ m) :=
  ⟨@call_cc⟩

  protected def lift [_root_.monad m] {α : Type u} (x : m α) : cont_t ρ m α :=
  ⟨λ cc, x >>= cc⟩

  instance [_root_.monad m] : has_monad_lift m (cont_t ρ m) :=
  ⟨@cont_t.lift _⟩

  -- there is NO instance of `monad_functor` for `cont_t`
end
end cont_t


namespace cont_t
  variable  {ρ : Type u}
  variable  {m : Type u → Type v}
  variables {α β : Type u}
  variables (x : cont_t ρ m α)

  lemma ext {x x' : cont_t ρ m α} (h : ∀ cc, x.run cc = x'.run cc) : x = x' :=
  by cases x; cases x'; simp [show x = x', from funext h]

  @[simp] lemma run_pure (a : α) (cc : α → m ρ) : (pure a : cont_t ρ m α).run cc = cc a := rfl
  @[simp] lemma run_bind (f : α → cont_t ρ m β) (cc : β → m ρ) :
    (x >>= f).run cc = x.run (λ a, (f a).run cc) := rfl
  @[simp] lemma run_map (f : α → β) (cc : β → m ρ) : (f <$> x).run cc = x.run (cc ∘ f) := rfl
end cont_t


instance (ρ : Type u) (m : Type u → Type v) [monad m] [is_lawful_monad m] : is_lawful_monad (cont_t ρ m) :=
{ id_map := by intros; apply cont_t.ext; simp,
  pure_bind := by intros; apply cont_t.ext; simp,
  bind_assoc := by intros; apply cont_t.ext; simp }
-- count the even numbers from 0 to 7 in a horrible, imperative way
def cont_example : cont_t unit (state_t ℕ io) ℕ :=
do call_cc $ λ break,
    (list.range 10).mmap' $ λ i,
      call_cc $ λ continue, do {
        when (i % 2 = 0) $
          continue (),
        when (i > 7) $
          break (),
        modify (+1) >> pure ()
      },
   get

#eval do ((), 4) ← (cont_example.run (λ _, pure ())).run 0,
         pure ()
