/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Jeremy Avigad, Floris van Doorn
-/
prelude
import init.logic init.wf

notation `Σ` binders `, ` r:(scoped p, sigma p) := r
notation `Σ'` binders `, ` r:(scoped p, psigma p) := r

universes u v

lemma ex_of_psig {α : Type u} {p : α → Prop} : (Σ' x, p x) → ∃ x, p x
| ⟨x, hx⟩ := ⟨x, hx⟩

section
variables {α : Type u} {β : α → Type v}

protected lemma sigma.eq : ∀ {p₁ p₂ : Σ a : α, β a} (h₁ : p₁.1 = p₂.1), (eq.rec_on h₁ p₁.2 : β p₂.1) = p₂.2 → p₁ = p₂
| ⟨a, b⟩ ⟨.(a), .(b)⟩ rfl rfl := rfl
end

section
variables {α : Sort u} {β : α → Sort v}

protected lemma psigma.eq : ∀ {p₁ p₂ : psigma β} (h₁ : p₁.1 = p₂.1), (eq.rec_on h₁ p₁.2 : β p₂.1) = p₂.2 → p₁ = p₂
| ⟨a, b⟩ ⟨.(a), .(b)⟩ rfl rfl := rfl
end
