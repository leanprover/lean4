/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Jeremy Avigad, Floris van Doorn
-/
prelude
import init.datatypes init.num init.wf init.logic

definition dpair := @sigma.mk
notation `Σ` binders `, ` r:(scoped P, sigma P) := r

lemma ex_of_sig {A : Type} {P : A → Prop} : (Σ x, P x) → ∃ x, P x
| (sigma.mk x hx) := exists.intro x hx

namespace sigma
  notation `pr₁`  := pr1
  notation `pr₂`  := pr2

  namespace ops
  postfix `.1`:(max+1) := pr1
  postfix `.2`:(max+1) := pr2
  end ops

  open ops well_founded

  section
  variables {A : Type} {B : A → Type}
  variable  (Ra  : A → A → Prop)
  variable  (Rb  : ∀ a, B a → B a → Prop)

  theorem dpair_eq : ∀ {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂} (H₁ : a₁ = a₂), eq.rec_on H₁ b₁ = b₂ → (sigma.mk a₁ b₁) = (sigma.mk a₂ b₂)
  | a₁ _ b₁ _ (eq.refl _) (eq.refl _) := rfl

  protected theorem eq {p₁ p₂ : Σa : A, B a} :
    ∀(H₁ : p₁.1 = p₂.1) (H₂ : eq.rec_on H₁ p₁.2 = p₂.2), p₁ = p₂ :=
  destruct p₁ (take a₁ b₁, destruct p₂ (take a₂ b₂ H₁ H₂, dpair_eq H₁ H₂))

  end
end sigma
