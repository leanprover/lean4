/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.ordered_group init.ring

/- Make sure instances defined in this file have lower priority than the ones
   defined for concrete structures -/
set_option default_priority 100

universe variable u

structure ordered_semiring (α : Type u)
  extends semiring α, ordered_mul_cancel_comm_monoid α renaming
  mul→add mul_assoc→add_assoc one→zero one_mul→zero_add mul_one→add_zero mul_comm→add_comm
  mul_left_cancel→add_left_cancel mul_right_cancel→add_right_cancel
  mul_le_mul_left→add_le_add_left mul_lt_mul_left→add_lt_add_left
  le_of_mul_le_mul_left→le_of_add_le_add_left
  lt_of_mul_lt_mul_left→lt_of_add_lt_add_left :=
(mul_le_mul_of_nonneg_left:  ∀ a b c : α, a ≤ b → 0 ≤ c → c * a ≤ c * b)
(mul_le_mul_of_nonneg_right: ∀ a b c : α, a ≤ b → 0 ≤ c → a * c ≤ b * c)
(mul_lt_mul_of_pos_left:     ∀ a b c : α, a < b → 0 < c → c * a < c * b)
(mul_lt_mul_of_pos_right:    ∀ a b c : α, a < b → 0 < c → a * c < b * c)

/- we make it a class now (and not as part of the structure) to avoid
   ordered_semiring.to_ordered_mul_cancel_comm_monoid to be an instance -/
attribute [class] ordered_semiring

variable {α : Type u}

instance add_comm_group_of_ordered_semiring (α : Type u) [s : ordered_semiring α] : semiring α :=
@ordered_semiring.to_semiring α s

instance monoid_of_ordered_semiring (α : Type u) [s : ordered_semiring α] : ordered_cancel_comm_monoid α :=
@ordered_semiring.to_ordered_mul_cancel_comm_monoid α s

section
variable [ordered_semiring α]

lemma mul_le_mul_of_nonneg_left {a b c : α} (h₁ : a ≤ b) (h₂ : 0 ≤ c) : c * a ≤ c * b :=
ordered_semiring.mul_le_mul_of_nonneg_left _ a b c h₁ h₂

lemma mul_le_mul_of_nonneg_right {a b c : α} (h₁ : a ≤ b) (h₂ : 0 ≤ c) : a * c ≤ b * c :=
ordered_semiring.mul_le_mul_of_nonneg_right _ a b c h₁ h₂

lemma mul_lt_mul_of_pos_left {a b c : α} (h₁ : a < b) (h₂ : 0 < c) : c * a < c * b :=
ordered_semiring.mul_lt_mul_of_pos_left _ a b c h₁ h₂

lemma mul_lt_mul_of_pos_right {a b c : α} (h₁ : a < b) (h₂ : 0 < c) : a * c < b * c :=
ordered_semiring.mul_lt_mul_of_pos_right _ a b c h₁ h₂
end

class linear_ordered_semiring (α : Type u) extends ordered_semiring α, linear_strong_order_pair α :=
(zero_lt_one : zero < one)

lemma zero_lt_one [linear_ordered_semiring α] : 0 < (1:α) :=
linear_ordered_semiring.zero_lt_one α

class decidable_linear_ordered_semiring (α : Type u) extends linear_ordered_semiring α, decidable_linear_order α
