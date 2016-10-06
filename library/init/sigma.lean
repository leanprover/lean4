/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Jeremy Avigad, Floris van Doorn
-/
prelude
import init.logic init.num init.wf

notation `Σ` binders `, ` r:(scoped P, sigma P) := r

universe variables u v

lemma ex_of_sig {A : Type u} {P : A → Prop} : (Σ x, P x) → ∃ x, P x
| ⟨x, hx⟩ := ⟨x, hx⟩

namespace sigma
  variables {A : Type u} {B : A → Type v}

  protected lemma eq : ∀ {p₁ p₂ : Σ a : A, B a} (H₁ : p₁.1 = p₂.1), (eq.rec_on H₁ p₁.2 : B p₂.1) = p₂.2 → p₁ = p₂
  | ⟨a, b⟩ ⟨.a, .b⟩ rfl rfl := rfl

end sigma
