/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Jeremy Avigad
-/
prelude
import init.logic
universes u v

instance {α : Type u} {β : Type v} [inhabited α] [inhabited β] : inhabited (prod α β) :=
⟨(default α, default β)⟩

instance {α : Type u} {β : Type v} [h₁ : decidable_eq α] [h₂ : decidable_eq β] : decidable_eq (α × β)
| (a, b) (a', b') :=
  match (h₁ a a') with
  | (is_true e₁) :=
    match (h₂ b b') with
    | (is_true e₂)  := is_true (eq.rec_on e₁ (eq.rec_on e₂ rfl))
    | (is_false n₂) := is_false (assume h, prod.no_confusion h (λ e₁' e₂', absurd e₂' n₂))
    end
  | (is_false n₁) := is_false (assume h, prod.no_confusion h (λ e₁' e₂', absurd e₁' n₁))
  end
