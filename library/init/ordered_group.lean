/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.group

universe variable u
variable α : Type u

class ordered_mul_cancel_comm_monoid (α : Type u)
      extends comm_monoid α, left_cancel_semigroup α,
              right_cancel_semigroup α, order_pair α :=
(mul_le_mul_left       : ∀ a b : α, a ≤ b → ∀ c : α, c * a ≤ c * b)
(le_of_mul_le_mul_left : ∀ a b c : α, a * b ≤ a * c → b ≤ c)
(mul_lt_mul_left       : ∀ a b : α, a < b → ∀ c : α, c * a < c * b)
(lt_of_mul_lt_mul_left : ∀ a b c : α, a * b < a * c → b < c)

@[class] def ordered_cancel_comm_monoid : Type u → Type (max 1 u) :=
ordered_mul_cancel_comm_monoid

instance add_comm_monoid_of_ordered_cancel_comm_monoid
  (α : Type u) [s : ordered_cancel_comm_monoid α] : add_comm_monoid α :=
@ordered_mul_cancel_comm_monoid.to_comm_monoid α s

instance add_left_cancel_semigroup_of_ordered_cancel_comm_monoid
  (α : Type u) [s : ordered_cancel_comm_monoid α] : add_left_cancel_semigroup α :=
@ordered_mul_cancel_comm_monoid.to_left_cancel_semigroup α s

instance add_right_cancel_semigroup_of_ordered_cancel_comm_monoid
  (α : Type u) [s : ordered_cancel_comm_monoid α] : add_right_cancel_semigroup α :=
@ordered_mul_cancel_comm_monoid.to_right_cancel_semigroup α s

instance order_pair_of_ordered_cancel_comm_monoid
  (α : Type u) [s : ordered_cancel_comm_monoid α] : order_pair α :=
@ordered_mul_cancel_comm_monoid.to_order_pair α s

section
variables [s : ordered_cancel_comm_monoid α]

lemma add_le_add_left {a b : α} (h : a ≤ b) (c : α) : c + a ≤ c + b :=
@ordered_mul_cancel_comm_monoid.mul_le_mul_left α s a b h c

lemma le_of_add_le_add_left {a b c : α} (h : a + b ≤ a + c) : b ≤ c :=
@ordered_mul_cancel_comm_monoid.le_of_mul_le_mul_left α s a b c h

lemma add_lt_add_left {a b : α} (h : a < b) (c : α) : c + a < c + b :=
@ordered_mul_cancel_comm_monoid.mul_lt_mul_left α s a b h c

lemma lt_of_add_lt_add_left {a b c : α} (h : a + b < a + c) : b < c :=
@ordered_mul_cancel_comm_monoid.lt_of_mul_lt_mul_left α s a b c h
end

class ordered_mul_comm_group (α : Type u) extends comm_group α, order_pair α :=
(mul_le_mul_left : ∀ a b : α, a ≤ b → ∀ c : α, c * a ≤ c * b)
(mul_lt_mul_left : ∀ a b : α, a < b → ∀ c : α, c * a < c * b)

@[class] def ordered_comm_group : Type u → Type (max 1 u) :=
ordered_mul_comm_group

instance add_comm_group_of_ordered_comm_group (α : Type u) [s : ordered_comm_group α] : add_comm_group α :=
@ordered_mul_comm_group.to_comm_group α s

lemma ordered_mul_comm_group.le_of_mul_le_mul_left [s : ordered_mul_comm_group α] {a b c : α}
  (h : a * b ≤ a * c) : b ≤ c :=
have a⁻¹ * (a * b) ≤ a⁻¹ * (a * c), from ordered_mul_comm_group.mul_le_mul_left _ _ h _,
begin simp [inv_mul_cancel_left] at this, assumption end

lemma ordered_mul_comm_group.lt_of_mul_lt_mul_left [s : ordered_mul_comm_group α] {a b c : α}
  (h : a * b < a * c) : b < c :=
have a⁻¹ * (a * b) < a⁻¹ * (a * c), from ordered_mul_comm_group.mul_lt_mul_left _ _ h _,
begin simp [inv_mul_cancel_left] at this, assumption end

instance ordered_mul_comm_group.to_ordered_mul_cancel_comm_monoid [s : ordered_mul_comm_group α] : ordered_mul_cancel_comm_monoid α :=
{ s with
  mul_left_cancel       := @mul_left_cancel α _,
  mul_right_cancel      := @mul_right_cancel α _,
  le_of_mul_le_mul_left := @ordered_mul_comm_group.le_of_mul_le_mul_left α _,
  lt_of_mul_lt_mul_left := @ordered_mul_comm_group.lt_of_mul_lt_mul_left α _ }

instance ordered_comm_group.to_ordered_cancel_comm_monoid  [s : ordered_comm_group α] : ordered_cancel_comm_monoid α :=
@ordered_mul_comm_group.to_ordered_mul_cancel_comm_monoid α s

class decidable_linear_ordered_mul_comm_group (α : Type u)
    extends comm_group α, decidable_linear_order α :=
(mul_le_mul_left : ∀ a b : α, a ≤ b → ∀ c : α, c * a ≤ c * b)
(mul_lt_mul_left : ∀ a b : α, a < b → ∀ c : α, c * a < c * b)

@[class] def decidable_linear_ordered_comm_group : Type u → Type (max 1 u) :=
decidable_linear_ordered_mul_comm_group

instance add_comm_group_of_decidable_linear_ordered_comm_group (α : Type u)
  [s : decidable_linear_ordered_comm_group α] : add_comm_group α :=
@decidable_linear_ordered_mul_comm_group.to_comm_group α s

instance decidable_linear_order_of_decidable_linear_ordered_comm_group (α : Type u)
  [s : decidable_linear_ordered_comm_group α] : decidable_linear_order α :=
@decidable_linear_ordered_mul_comm_group.to_decidable_linear_order α s

instance decidable_linear_ordered_mul_comm_group.to_ordered_mul_comm_group (α : Type u)
  [s : decidable_linear_ordered_mul_comm_group α] : ordered_mul_comm_group α :=
{s with
 le_of_lt := @le_of_lt α _,
 lt_of_le_of_lt := @lt_of_le_of_lt α _,
 lt_of_lt_of_le := @lt_of_lt_of_le α _ }

instance decidable_linear_ordered_comm_group.to_ordered_comm_group (α : Type u)
  [s : decidable_linear_ordered_comm_group α] : ordered_comm_group α :=
@decidable_linear_ordered_mul_comm_group.to_ordered_mul_comm_group α s
