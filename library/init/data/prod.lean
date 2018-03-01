/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Jeremy Avigad
-/
prelude
import init.logic
universes u v

section
variables {α : Type u} {β : Type v}

@[simp] lemma prod.mk.eta : ∀{p : α × β}, (p.1, p.2) = p
| (a, b) := rfl

instance [inhabited α] [inhabited β] : inhabited (prod α β) :=
⟨(default α, default β)⟩

instance [h₁ : decidable_eq α] [h₂ : decidable_eq β] : decidable_eq (α × β)
| (a, b) (a', b') :=
  match (h₁ a a') with
  | (is_true e₁) :=
    match (h₂ b b') with
    | (is_true e₂)  := is_true (eq.rec_on e₁ (eq.rec_on e₂ rfl))
    | (is_false n₂) := is_false (assume h, prod.no_confusion h (λ e₁' e₂', absurd e₂' n₂))
    end
  | (is_false n₁) := is_false (assume h, prod.no_confusion h (λ e₁' e₂', absurd e₁' n₁))
  end

instance [has_lt α] [has_lt β] : has_lt (α × β) :=
⟨λ s t, s.1 < t.1 ∨ (s.1 = t.1 ∧ s.2 < t.2)⟩

instance prod_has_decidable_lt
         [has_lt α] [has_lt β]
         [decidable_eq α] [decidable_eq β]
         [decidable_rel ((<) : α → α → Prop)]
         [decidable_rel ((<) : β → β → Prop)] : Π s t : α × β, decidable (s < t) :=
λ t s, or.decidable

lemma prod.lt_def [has_lt α] [has_lt β] (s t : α × β) : (s < t) = (s.1 < t.1 ∨ (s.1 = t.1 ∧ s.2 < t.2)) :=
rfl

end

def {u₁ u₂ v₁ v₂} prod.map {α₁ : Type u₁} {α₂ : Type u₂} {β₁ : Type v₁} {β₂ : Type v₂}
  (f : α₁ → α₂) (g : β₁ → β₂) : α₁ × β₁ → α₂ × β₂
| (a, b) := (f a, g b)
