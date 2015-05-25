/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
import data.bool
open bool

protected definition char.is_inhabited [instance] : inhabited char :=
inhabited.mk (char.mk ff ff ff ff ff ff ff ff)

protected definition string.is_inhabited [instance] : inhabited string :=
inhabited.mk string.empty

open decidable

definition decidable_eq_char [instance] : ∀ c₁ c₂ : char, decidable (c₁ = c₂) :=
begin
  intro c₁ c₂,
  cases c₁ with a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈,
  cases c₂ with b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈,
  apply (@by_cases (a₁ = b₁)), intros,
  apply (@by_cases (a₂ = b₂)), intros,
  apply (@by_cases (a₃ = b₃)), intros,
  apply (@by_cases (a₄ = b₄)), intros,
  apply (@by_cases (a₅ = b₅)), intros,
  apply (@by_cases (a₆ = b₆)), intros,
  apply (@by_cases (a₇ = b₇)), intros,
  apply (@by_cases (a₈ = b₈)), intros,
  left, congruence, repeat assumption,
  repeat (intro n; right; intro h; injection h; contradiction)
end

open string

definition decidable_eq_string [instance] : ∀ s₁ s₂ : string, decidable (s₁ = s₂)
| empty       empty       := by left; reflexivity
| empty       (str c₂ r₂) := by right; contradiction
| (str c₁ r₁) empty       := by right; contradiction
| (str c₁ r₁) (str c₂ r₂) :=
  match decidable_eq_char c₁ c₂ with
  | inl e₁ :=
    match decidable_eq_string r₁ r₂ with
    | inl e₂ := by left; congruence; repeat assumption
    | inr n₂ := by right; intro h; injection h; contradiction
    end
  | inr n₁ := by right; intro h; injection h; contradiction
  end
