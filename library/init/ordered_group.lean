/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
prelude
import init.group

/- Make sure instances defined in this file have lower priority than the ones
   defined for concrete structures -/
set_option default_priority 100

universe variable u

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
variable {α : Type u}
variable [s : ordered_cancel_comm_monoid α]

lemma add_le_add_left {a b : α} (h : a ≤ b) (c : α) : c + a ≤ c + b :=
@ordered_mul_cancel_comm_monoid.mul_le_mul_left α s a b h c

lemma le_of_add_le_add_left {a b c : α} (h : a + b ≤ a + c) : b ≤ c :=
@ordered_mul_cancel_comm_monoid.le_of_mul_le_mul_left α s a b c h

lemma add_lt_add_left {a b : α} (h : a < b) (c : α) : c + a < c + b :=
@ordered_mul_cancel_comm_monoid.mul_lt_mul_left α s a b h c

lemma lt_of_add_lt_add_left {a b c : α} (h : a + b < a + c) : b < c :=
@ordered_mul_cancel_comm_monoid.lt_of_mul_lt_mul_left α s a b c h
end

section
variable {α : Type u}
variable [ordered_cancel_comm_monoid α]

lemma add_le_add_right {a b : α} (h : a ≤ b) (c : α) : a + c ≤ b + c :=
add_comm c a ▸ add_comm c b ▸ add_le_add_left h c

theorem add_lt_add_right {a b : α} (h : a < b) (c : α) : a + c < b + c :=
begin
 rw [add_comm a c, add_comm b c],
 exact (add_lt_add_left h c)
end

lemma add_le_add {a b c d : α} (h₁ : a ≤ b) (h₂ : c ≤ d) : a + c ≤ b + d :=
le_trans (add_le_add_right h₁ c) (add_le_add_left h₂ b)

lemma le_add_of_nonneg_right {a b : α} (h : b ≥ 0) : a ≤ a + b :=
have a + b ≥ a + 0, from add_le_add_left h a,
by rwa add_zero at this

lemma le_add_of_nonneg_left {a b : α} (h : b ≥ 0) : a ≤ b + a :=
have 0 + a ≤ b + a, from add_le_add_right h a,
by rwa zero_add at this

lemma add_lt_add {a b c d : α} (h₁ : a < b) (h₂ : c < d) : a + c < b + d :=
lt_trans (add_lt_add_right h₁ c) (add_lt_add_left h₂ b)

lemma add_lt_add_of_le_of_lt {a b c d : α} (h₁ : a ≤ b) (h₂ : c < d) : a + c < b + d :=
lt_of_le_of_lt (add_le_add_right h₁ c) (add_lt_add_left h₂ b)

lemma add_lt_add_of_lt_of_le {a b c d : α} (h₁ : a < b) (h₂ : c ≤ d) : a + c < b + d :=
lt_of_lt_of_le (add_lt_add_right h₁ c) (add_le_add_left h₂ b)

lemma lt_add_of_pos_right (a : α) {b : α} (h : b > 0) : a < a + b :=
have a + 0 < a + b, from add_lt_add_left h a,
by rwa [add_zero] at this

lemma lt_add_of_pos_left (a : α) {b : α} (h : b > 0) : a < b + a :=
have 0 + a < b + a, from add_lt_add_right h a,
by rwa [zero_add] at this

lemma le_of_add_le_add_right {a b c : α} (h : a + b ≤ c + b) : a ≤ c :=
le_of_add_le_add_left
  (show b + a ≤ b + c, begin rw [add_comm b a, add_comm b c], assumption end)

lemma lt_of_add_lt_add_right {a b c : α} (h : a + b < c + b) : a < c :=
lt_of_add_lt_add_left
  (show b + a < b + c, begin rw [add_comm b a, add_comm b c], assumption end)
end

class ordered_mul_comm_group (α : Type u) extends comm_group α, order_pair α :=
(mul_le_mul_left : ∀ a b : α, a ≤ b → ∀ c : α, c * a ≤ c * b)
(mul_lt_mul_left : ∀ a b : α, a < b → ∀ c : α, c * a < c * b)

@[class] def ordered_comm_group : Type u → Type (max 1 u) :=
ordered_mul_comm_group

instance add_comm_group_of_ordered_comm_group (α : Type u) [s : ordered_comm_group α] : add_comm_group α :=
@ordered_mul_comm_group.to_comm_group α s

section
variable {α : Type u}
variable [ordered_mul_comm_group α]

lemma ordered_mul_comm_group.le_of_mul_le_mul_left {a b c : α} (h : a * b ≤ a * c) : b ≤ c :=
have a⁻¹ * (a * b) ≤ a⁻¹ * (a * c), from ordered_mul_comm_group.mul_le_mul_left _ _ h _,
begin simp [inv_mul_cancel_left] at this, assumption end

lemma ordered_mul_comm_group.lt_of_mul_lt_mul_left {a b c : α} (h : a * b < a * c) : b < c :=
have a⁻¹ * (a * b) < a⁻¹ * (a * c), from ordered_mul_comm_group.mul_lt_mul_left _ _ h _,
begin simp [inv_mul_cancel_left] at this, assumption end
end

instance ordered_mul_comm_group.to_ordered_mul_cancel_comm_monoid (α : Type u) [s : ordered_mul_comm_group α] : ordered_mul_cancel_comm_monoid α :=
{ s with
  mul_left_cancel       := @mul_left_cancel α _,
  mul_right_cancel      := @mul_right_cancel α _,
  le_of_mul_le_mul_left := @ordered_mul_comm_group.le_of_mul_le_mul_left α _,
  lt_of_mul_lt_mul_left := @ordered_mul_comm_group.lt_of_mul_lt_mul_left α _ }

instance ordered_comm_group.to_ordered_cancel_comm_monoid  (α : Type u) [s : ordered_comm_group α] : ordered_cancel_comm_monoid α :=
@ordered_mul_comm_group.to_ordered_mul_cancel_comm_monoid α s

section
variables {α : Type u} [ordered_comm_group α]

theorem neg_le_neg {a b : α} (h : a ≤ b) : -b ≤ -a :=
have 0 ≤ -a + b,           from add_left_neg a ▸ add_le_add_left h (-a),
have 0 + -b ≤ -a + b + -b, from add_le_add_right this (-b),
by rwa [add_neg_cancel_right, zero_add] at this

lemma le_of_neg_le_neg {a b : α} (h : -b ≤ -a) : a ≤ b :=
suffices -(-a) ≤ -(-b), from
  begin simp [neg_neg] at this, assumption end,
neg_le_neg h

lemma nonneg_of_neg_nonpos {a : α} (h : -a ≤ 0) : 0 ≤ a :=
have -a ≤ -0, by rwa neg_zero,
le_of_neg_le_neg this

lemma neg_nonpos_of_nonneg {a : α} (h : 0 ≤ a) : -a ≤ 0 :=
have -a ≤ -0, from neg_le_neg h,
by rwa neg_zero at this

lemma nonpos_of_neg_nonneg {a : α} (h : 0 ≤ -a) : a ≤ 0 :=
have -0 ≤ -a, by rwa neg_zero,
le_of_neg_le_neg this

lemma neg_nonneg_of_nonpos {a : α} (h : a ≤ 0) : 0 ≤ -a :=
have -0 ≤ -a, from neg_le_neg h,
by rwa neg_zero at this
end

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
