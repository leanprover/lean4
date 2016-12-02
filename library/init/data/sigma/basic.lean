/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Jeremy Avigad, Floris van Doorn
-/
prelude
import init.logic init.wf

notation `Σ` binders `, ` r:(scoped p, sigma p) := r

universe variables u v

lemma ex_of_sig {α : Type u} {p : α → Prop} : (Σ x, p x) → ∃ x, p x
| ⟨x, hx⟩ := ⟨x, hx⟩

namespace sigma
  variables {α : Type u} {β : α → Type v}

  protected lemma eq : ∀ {p₁ p₂ : Σ a : α, β a} (h₁ : p₁.1 = p₂.1), (eq.rec_on h₁ p₁.2 : β p₂.1) = p₂.2 → p₁ = p₂
  | ⟨a, b⟩ ⟨.a, .b⟩ rfl rfl := rfl

end sigma
