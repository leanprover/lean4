/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Leonardo de Moura

Classical proof that if f is injective, then f has a left inverse (if domain is not empty).
This proof does not use Hilbert's choice, but the simpler axiom of choice which is just a proposition.
-/
import logic.axioms.classical
open function

-- The forall_not_of_not_exists at logic.axioms uses decidable.
theorem forall_not_of_not_exists {A : Type} {p : A → Prop}
  (H : ¬∃x, p x) : ∀x, ¬p x :=
take x, or.elim (em (p x))
  (assume Hp : p x,   absurd (exists.intro x Hp) H)
  (assume Hnp : ¬p x, Hnp)

theorem has_left_inverse_of_injective {A B : Type} {f : A → B} : nonempty A → injective f → ∃ g, ∀ x, g (f x) = x :=
suppose nonempty A,
assume inj : ∀ a₁ a₂, f a₁ = f a₂ → a₁ = a₂,
have ∃ g : B → A, ∀ b, (∀ a, f a = b → g b = a) ∨ (∀ a, f a ≠ b), from
  axiom_of_choice (λ b : B, or.elim (em (∃ a, f a = b))
    (suppose (∃ a, f a = b),
       obtain w `f w = b`, from this,
       exists.intro w (or.inl (take a,
         suppose f a = b,
         have    f w = f a, begin subst this, exact `f w = f a` end,
         inj w a `f w = f a`)))
    (suppose ¬(∃ a, f a = b),
     obtain a, from `nonempty A`,
     exists.intro a (or.inr (forall_not_of_not_exists this)))),
obtain g hg, from this,
exists.intro g (take a,
or.elim (hg (f a))
  (suppose (∀ a₁, f a₁ = f a → g (f a) = a₁),
    this a rfl)
  (suppose (∀ a₁, f a₁ ≠ f a),
    absurd rfl (this a)))
