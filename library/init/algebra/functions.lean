/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
prelude
import init.algebra.ordered_group

universe variables u

definition min {α : Type u} [decidable_linear_order α] (a b : α) : α := if a ≤ b then a else b
definition max {α : Type u} [decidable_linear_order α] (a b : α) : α := if a ≤ b then b else a
definition abs {α : Type u} [decidable_linear_ordered_comm_group α] (a : α) : α := max a (-a)

section
open decidable tactic
variables {α : Type u} [decidable_linear_order α]

private meta def min_tac_step : tactic unit :=
solve1 $ intros
>> `[unfold min max]
>> try `[simp_using_hs [if_pos, if_neg]]
>> try `[apply le_refl]
>> try `[apply le_of_not_le, assumption]

meta def tactic.interactive.min_tac (a b : tactic.interactive.types.qexpr) : tactic unit :=
`[apply @by_cases (%%a ≤ %%b), repeat {min_tac_step}]

theorem min_le_left (a b : α) : min a b ≤ a :=
by min_tac a b

theorem min_le_right (a b : α) : min a b ≤ b :=
by min_tac a b

theorem le_min {a b c : α} (h₁ : c ≤ a) (h₂ : c ≤ b) : c ≤ min a b :=
by min_tac a b

theorem le_max_left (a b : α) : a ≤ max a b :=
by min_tac a b

theorem le_max_right (a b : α) : b ≤ max a b :=
by min_tac a b

theorem max_le {a b c : α} (h₁ : a ≤ c) (h₂ : b ≤ c) : max a b ≤ c :=
by min_tac a b

theorem eq_min {a b c : α} (h₁ : c ≤ a) (h₂ : c ≤ b) (h₃ : ∀{d}, d ≤ a → d ≤ b → d ≤ c) :  c = min a b :=
le_antisymm (le_min h₁ h₂) (h₃ (min_le_left a b) (min_le_right a b))

theorem min_comm (a b : α) : min a b = min b a :=
eq_min (min_le_right a b) (min_le_left a b) (λ c h₁ h₂, le_min h₂ h₁)

theorem min_assoc (a b c : α) : min (min a b) c = min a (min b c) :=
begin
  apply eq_min,
  { apply le_trans, apply min_le_left, apply min_le_left },
  { apply le_min, apply le_trans, apply min_le_left, apply min_le_right, apply min_le_right },
  { intros d h₁ h₂, apply le_min, apply le_min h₁, apply le_trans h₂, apply min_le_left,
    apply le_trans h₂, apply min_le_right }
end

theorem min_left_comm : ∀ (a b c : α), min a (min b c) = min b (min a c) :=
left_comm (@min α _) (@min_comm α _) (@min_assoc α _)

theorem min_self (a : α) : min a a = a :=
by min_tac a a

theorem min_eq_left {a b : α} (h : a ≤ b) : min a b = a :=
begin apply eq.symm, apply eq_min (le_refl _) h, intros, assumption end

theorem min_eq_right {a b : α} (h : b ≤ a) : min a b = b :=
eq.subst (min_comm b a) (min_eq_left h)

theorem eq_max {a b c : α} (h₁ : a ≤ c) (h₂ : b ≤ c) (h₃ : ∀{d}, a ≤ d → b ≤ d → c ≤ d) : c = max a b :=
le_antisymm (h₃ (le_max_left a b) (le_max_right a b)) (max_le h₁ h₂)

theorem max_comm (a b : α) : max a b = max b a :=
eq_max (le_max_right a b) (le_max_left a b) (λ c h₁ h₂, max_le h₂ h₁)

theorem max_assoc (a b c : α) : max (max a b) c = max a (max b c) :=
begin
  apply eq_max,
  { apply le_trans, apply le_max_left a b, apply le_max_left },
  { apply max_le, apply le_trans, apply le_max_right a b, apply le_max_left, apply le_max_right },
  { intros d h₁ h₂, apply max_le, apply max_le h₁, apply le_trans (le_max_left _ _) h₂,
    apply le_trans (le_max_right _ _) h₂}
end

theorem max_left_comm : ∀ (a b c : α), max a (max b c) = max b (max a c) :=
left_comm (@max α _) (@max_comm α _) (@max_assoc α _)

theorem max_self (a : α) : max a a = a :=
by min_tac a a

theorem max_eq_left {a b : α} (h : b ≤ a) : max a b = a :=
begin apply eq.symm, apply eq_max (le_refl _) h, intros, assumption end

theorem max_eq_right {a b : α} (h : a ≤ b) : max a b = b :=
eq.subst (max_comm b a) (max_eq_left h)

/- these rely on lt_of_lt -/

theorem min_eq_left_of_lt {a b : α} (h : a < b) : min a b = a :=
min_eq_left (le_of_lt h)

theorem min_eq_right_of_lt {a b : α} (h : b < a) : min a b = b :=
min_eq_right (le_of_lt h)

theorem max_eq_left_of_lt {a b : α} (h : b < a) : max a b = a :=
max_eq_left (le_of_lt h)

theorem max_eq_right_of_lt {a b : α} (h : a < b) : max a b = b :=
max_eq_right (le_of_lt h)

/- these use the fact that it is a linear ordering -/

theorem lt_min {a b c : α} (h₁ : a < b) (h₂ : a < c) : a < min b c :=
or.elim (le_or_gt b c)
  (assume h : b ≤ c, by min_tac b c)
  (assume h : b > c, by min_tac b c)

theorem max_lt {a b c : α} (h₁ : a < c) (h₂ : b < c) : max a b < c :=
or.elim (le_or_gt a b)
  (assume h : a ≤ b, by min_tac a b)
  (assume h : a > b, by min_tac a b)
end
