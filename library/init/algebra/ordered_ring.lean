/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
prelude
import init.algebra.ordered_group init.algebra.ring

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

structure ordered_ring (α : Type u) extends ring α, ordered_mul_comm_group α renaming
  mul→add mul_assoc→add_assoc one→zero one_mul→zero_add mul_one→add_zero inv→neg
  mul_left_inv→add_left_inv mul_comm→add_comm mul_le_mul_left→add_le_add_left
  mul_lt_mul_left→add_lt_add_left, zero_ne_one_class α :=
(mul_nonneg : ∀ a b : α, 0 ≤ a → 0 ≤ b → 0 ≤ a * b)
(mul_pos    : ∀ a b : α, 0 < a → 0 < b → 0 < a * b)

/- we make it a class now (and not as part of the structure) to avoid
   ordered_ring.to_ordered_mul_comm_group to be an instance -/
attribute [class] ordered_ring

instance add_comm_group_of_ordered_ring (α : Type u) [s : ordered_ring α] : ring α :=
@ordered_ring.to_ring α s

instance monoid_of_ordered_ring (α : Type u) [s : ordered_ring α] : ordered_comm_group α :=
@ordered_ring.to_ordered_mul_comm_group α s

instance zero_ne_one_class_of_ordered_ring (α : Type u) [s : ordered_ring α] : zero_ne_one_class α :=
@ordered_ring.to_zero_ne_one_class α s

lemma ordered_ring.mul_le_mul_of_nonneg_left [s : ordered_ring α] {a b c : α}
        (h₁ : a ≤ b) (h₂ : 0 ≤ c) : c * a ≤ c * b :=
have 0 ≤ b - a,       from sub_nonneg_of_le h₁,
have 0 ≤ c * (b - a), from ordered_ring.mul_nonneg s c (b - a) h₂ this,
begin
  rw mul_sub_left_distrib at this,
  apply le_of_sub_nonneg this
end

lemma ordered_ring.mul_le_mul_of_nonneg_right [s : ordered_ring α] {a b c : α}
      (h₁ : a ≤ b) (h₂ : 0 ≤ c) : a * c ≤ b * c  :=
have 0 ≤ b - a,       from sub_nonneg_of_le h₁,
have 0 ≤ (b - a) * c, from ordered_ring.mul_nonneg s (b - a) c this h₂,
begin
  rw mul_sub_right_distrib at this,
  apply le_of_sub_nonneg this
end

lemma ordered_ring.mul_lt_mul_of_pos_left [s : ordered_ring α] {a b c : α}
       (h₁ : a < b) (h₂ : 0 < c) : c * a < c * b :=
have 0 < b - a,       from sub_pos_of_lt h₁,
have 0 < c * (b - a), from ordered_ring.mul_pos s c (b - a) h₂ this,
begin
  rw mul_sub_left_distrib at this,
  apply lt_of_sub_pos this
end

lemma ordered_ring.mul_lt_mul_of_pos_right [s : ordered_ring α] {a b c : α}
      (h₁ : a < b) (h₂ : 0 < c) : a * c < b * c :=
have 0 < b - a,       from sub_pos_of_lt h₁,
have 0 < (b - a) * c, from ordered_ring.mul_pos s (b - a) c this h₂,
begin
  rw mul_sub_right_distrib at this,
  apply lt_of_sub_pos this
end

instance ordered_ring.to_ordered_semiring [s : ordered_ring α] : ordered_semiring α :=
{ s with
  mul_zero                   := mul_zero,
  zero_mul                   := zero_mul,
  add_left_cancel            := @add_left_cancel α _,
  add_right_cancel           := @add_right_cancel α _,
  le_of_add_le_add_left      := @le_of_add_le_add_left α _,
  mul_le_mul_of_nonneg_left  := @ordered_ring.mul_le_mul_of_nonneg_left α _,
  mul_le_mul_of_nonneg_right := @ordered_ring.mul_le_mul_of_nonneg_right α _,
  mul_lt_mul_of_pos_left     := @ordered_ring.mul_lt_mul_of_pos_left α _,
  mul_lt_mul_of_pos_right    := @ordered_ring.mul_lt_mul_of_pos_right α _,
  lt_of_add_lt_add_left      := @lt_of_add_lt_add_left α _}

class linear_ordered_ring (α : Type u) extends ordered_ring α, linear_strong_order_pair α :=
(zero_lt_one : lt zero one)

instance linear_ordered_ring.to_linear_ordered_semiring [s : linear_ordered_ring α] : linear_ordered_semiring α :=
{ s with
  mul_zero                   := mul_zero,
  zero_mul                   := zero_mul,
  add_left_cancel            := @add_left_cancel α _,
  add_right_cancel           := @add_right_cancel α _,
  le_of_add_le_add_left      := @le_of_add_le_add_left α _,
  mul_le_mul_of_nonneg_left  := @mul_le_mul_of_nonneg_left α _,
  mul_le_mul_of_nonneg_right := @mul_le_mul_of_nonneg_right α _,
  mul_lt_mul_of_pos_left     := @mul_lt_mul_of_pos_left α _,
  mul_lt_mul_of_pos_right    := @mul_lt_mul_of_pos_right α _,
  le_total                   := linear_ordered_ring.le_total,
  lt_of_add_lt_add_left      := @lt_of_add_lt_add_left α _ }
