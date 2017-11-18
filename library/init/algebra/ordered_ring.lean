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

set_option old_structure_cmd true

universe u

class ordered_semiring (α : Type u)
  extends semiring α, ordered_cancel_comm_monoid α :=
(mul_le_mul_of_nonneg_left:  ∀ a b c : α, a ≤ b → 0 ≤ c → c * a ≤ c * b)
(mul_le_mul_of_nonneg_right: ∀ a b c : α, a ≤ b → 0 ≤ c → a * c ≤ b * c)
(mul_lt_mul_of_pos_left:     ∀ a b c : α, a < b → 0 < c → c * a < c * b)
(mul_lt_mul_of_pos_right:    ∀ a b c : α, a < b → 0 < c → a * c < b * c)

variable {α : Type u}

section ordered_semiring
variable [ordered_semiring α]

lemma mul_le_mul_of_nonneg_left {a b c : α} (h₁ : a ≤ b) (h₂ : 0 ≤ c) : c * a ≤ c * b :=
ordered_semiring.mul_le_mul_of_nonneg_left a b c h₁ h₂

lemma mul_le_mul_of_nonneg_right {a b c : α} (h₁ : a ≤ b) (h₂ : 0 ≤ c) : a * c ≤ b * c :=
ordered_semiring.mul_le_mul_of_nonneg_right a b c h₁ h₂

lemma mul_lt_mul_of_pos_left {a b c : α} (h₁ : a < b) (h₂ : 0 < c) : c * a < c * b :=
ordered_semiring.mul_lt_mul_of_pos_left a b c h₁ h₂

lemma mul_lt_mul_of_pos_right {a b c : α} (h₁ : a < b) (h₂ : 0 < c) : a * c < b * c :=
ordered_semiring.mul_lt_mul_of_pos_right a b c h₁ h₂

-- TODO: there are four variations, depending on which variables we assume to be nonneg
lemma mul_le_mul {a b c d : α} (hac : a ≤ c) (hbd : b ≤ d) (nn_b : 0 ≤ b) (nn_c : 0 ≤ c) : a * b ≤ c * d :=
calc
  a * b ≤ c * b : mul_le_mul_of_nonneg_right hac nn_b
    ... ≤ c * d : mul_le_mul_of_nonneg_left hbd nn_c

lemma mul_nonneg {a b : α} (ha : a ≥ 0) (hb : b ≥ 0) : a * b ≥ 0 :=
have h : 0 * b ≤ a * b, from mul_le_mul_of_nonneg_right ha hb,
by rwa [zero_mul] at h

lemma mul_nonpos_of_nonneg_of_nonpos {a b : α} (ha : a ≥ 0) (hb : b ≤ 0) : a * b ≤ 0 :=
have h : a * b ≤ a * 0, from mul_le_mul_of_nonneg_left hb ha,
by rwa mul_zero at h

lemma mul_nonpos_of_nonpos_of_nonneg {a b : α} (ha : a ≤ 0) (hb : b ≥ 0) : a * b ≤ 0 :=
have h : a * b ≤ 0 * b, from mul_le_mul_of_nonneg_right ha hb,
by rwa zero_mul at h

lemma mul_lt_mul {a b c d : α} (hac : a < c) (hbd : b ≤ d) (pos_b : 0 < b) (nn_c : 0 ≤ c) :  a * b < c * d :=
calc
  a * b < c * b : mul_lt_mul_of_pos_right hac pos_b
    ... ≤ c * d : mul_le_mul_of_nonneg_left hbd nn_c

lemma mul_lt_mul' {a b c d : α} (h1 : a ≤ c) (h2 : b < d) (h3 : b ≥ 0) (h4 : c > 0) :
       a * b < c * d :=
calc
   a * b ≤ c * b : mul_le_mul_of_nonneg_right h1 h3
     ... < c * d : mul_lt_mul_of_pos_left h2 h4

lemma mul_pos {a b : α} (ha : a > 0) (hb : b > 0) : a * b > 0 :=
have h : 0 * b < a * b, from mul_lt_mul_of_pos_right ha hb,
by rwa zero_mul at h

lemma mul_neg_of_pos_of_neg {a b : α} (ha : a > 0) (hb : b < 0) : a * b < 0 :=
have h : a * b < a * 0, from mul_lt_mul_of_pos_left hb ha,
by rwa mul_zero at h

lemma mul_neg_of_neg_of_pos {a b : α} (ha : a < 0) (hb : b > 0) : a * b < 0 :=
have h : a * b < 0 * b, from mul_lt_mul_of_pos_right ha hb,
by rwa zero_mul at  h

lemma mul_self_le_mul_self {a b : α} (h1 : 0 ≤ a) (h2 : a ≤ b) : a * a ≤ b * b :=
mul_le_mul h2 h2 h1 (le_trans h1 h2)

lemma mul_self_lt_mul_self {a b : α} (h1 : 0 ≤ a) (h2 : a < b) : a * a < b * b :=
mul_lt_mul' (le_of_lt h2) h2 h1 (lt_of_le_of_lt h1 h2)
end ordered_semiring

class linear_ordered_semiring (α : Type u) extends ordered_semiring α, linear_order α :=
(zero_lt_one : zero < one)

section linear_ordered_semiring
variable [linear_ordered_semiring α]

lemma zero_lt_one : 0 < (1:α) :=
linear_ordered_semiring.zero_lt_one α

lemma zero_le_one : 0 ≤ (1:α) :=
le_of_lt zero_lt_one

lemma lt_of_mul_lt_mul_left {a b c : α} (h : c * a < c * b) (hc : c ≥ 0) : a < b :=
lt_of_not_ge
  (assume h1 : b ≤ a,
   have h2 : c * b ≤ c * a, from mul_le_mul_of_nonneg_left h1 hc,
   not_lt_of_ge h2 h)

lemma lt_of_mul_lt_mul_right {a b c : α} (h : a * c < b * c) (hc : c ≥ 0) : a < b :=
lt_of_not_ge
  (assume h1 : b ≤ a,
   have h2 : b * c ≤ a * c, from mul_le_mul_of_nonneg_right h1 hc,
   not_lt_of_ge h2 h)

lemma le_of_mul_le_mul_left {a b c : α} (h : c * a ≤ c * b) (hc : c > 0) : a ≤ b :=
le_of_not_gt
  (assume h1 : b < a,
   have h2 : c * b < c * a, from mul_lt_mul_of_pos_left h1 hc,
   not_le_of_gt h2 h)

lemma le_of_mul_le_mul_right {a b c : α} (h : a * c ≤ b * c) (hc : c > 0) : a ≤ b :=
le_of_not_gt
  (assume h1 : b < a,
   have h2 : b * c < a * c, from mul_lt_mul_of_pos_right h1 hc,
   not_le_of_gt h2 h)

lemma pos_of_mul_pos_left {a b : α} (h : 0 < a * b) (h1 : 0 ≤ a) : 0 < b :=
lt_of_not_ge
  (assume h2 : b ≤ 0,
   have h3 : a * b ≤ 0, from mul_nonpos_of_nonneg_of_nonpos h1 h2,
   not_lt_of_ge h3 h)

lemma pos_of_mul_pos_right {a b : α} (h : 0 < a * b) (h1 : 0 ≤ b) : 0 < a :=
lt_of_not_ge
  (assume h2 : a ≤ 0,
   have h3 : a * b ≤ 0, from mul_nonpos_of_nonpos_of_nonneg h2 h1,
   not_lt_of_ge h3 h)

lemma nonneg_of_mul_nonneg_left {a b : α} (h : 0 ≤ a * b) (h1 : 0 < a) : 0 ≤ b :=
le_of_not_gt
  (assume h2 : b < 0,
   not_le_of_gt (mul_neg_of_pos_of_neg h1 h2) h)

lemma nonneg_of_mul_nonneg_right {a b : α} (h : 0 ≤ a * b) (h1 : 0 < b) : 0 ≤ a :=
le_of_not_gt
  (assume h2 : a < 0,
   not_le_of_gt (mul_neg_of_neg_of_pos h2 h1) h)

lemma neg_of_mul_neg_left {a b : α} (h : a * b < 0) (h1 : 0 ≤ a) : b < 0 :=
lt_of_not_ge
  (assume h2 : b ≥ 0,
   not_lt_of_ge (mul_nonneg h1 h2) h)

lemma neg_of_mul_neg_right {a b : α} (h : a * b < 0) (h1 : 0 ≤ b) : a < 0 :=
lt_of_not_ge
  (assume h2 : a ≥ 0,
   not_lt_of_ge (mul_nonneg h2 h1) h)

lemma nonpos_of_mul_nonpos_left {a b : α} (h : a * b ≤ 0) (h1 : 0 < a) : b ≤ 0 :=
le_of_not_gt
  (assume h2 : b > 0,
   not_le_of_gt (mul_pos h1 h2) h)

lemma nonpos_of_mul_nonpos_right {a b : α} (h : a * b ≤ 0) (h1 : 0 < b) : a ≤ 0 :=
le_of_not_gt
  (assume h2 : a > 0,
   not_le_of_gt (mul_pos h2 h1) h)

end linear_ordered_semiring

class decidable_linear_ordered_semiring (α : Type u) extends linear_ordered_semiring α, decidable_linear_order α

class ordered_ring (α : Type u) extends ring α, ordered_comm_group α, zero_ne_one_class α :=
(mul_nonneg : ∀ a b : α, 0 ≤ a → 0 ≤ b → 0 ≤ a * b)
(mul_pos    : ∀ a b : α, 0 < a → 0 < b → 0 < a * b)

lemma ordered_ring.mul_le_mul_of_nonneg_left [s : ordered_ring α] {a b c : α}
        (h₁ : a ≤ b) (h₂ : 0 ≤ c) : c * a ≤ c * b :=
have 0 ≤ b - a,       from sub_nonneg_of_le h₁,
have 0 ≤ c * (b - a), from ordered_ring.mul_nonneg c (b - a) h₂ this,
begin
  rw mul_sub_left_distrib at this,
  apply le_of_sub_nonneg this
end

lemma ordered_ring.mul_le_mul_of_nonneg_right [s : ordered_ring α] {a b c : α}
      (h₁ : a ≤ b) (h₂ : 0 ≤ c) : a * c ≤ b * c  :=
have 0 ≤ b - a,       from sub_nonneg_of_le h₁,
have 0 ≤ (b - a) * c, from ordered_ring.mul_nonneg (b - a) c this h₂,
begin
  rw mul_sub_right_distrib at this,
  apply le_of_sub_nonneg this
end

lemma ordered_ring.mul_lt_mul_of_pos_left [s : ordered_ring α] {a b c : α}
       (h₁ : a < b) (h₂ : 0 < c) : c * a < c * b :=
have 0 < b - a,       from sub_pos_of_lt h₁,
have 0 < c * (b - a), from ordered_ring.mul_pos c (b - a) h₂ this,
begin
  rw mul_sub_left_distrib at this,
  apply lt_of_sub_pos this
end

lemma ordered_ring.mul_lt_mul_of_pos_right [s : ordered_ring α] {a b c : α}
      (h₁ : a < b) (h₂ : 0 < c) : a * c < b * c :=
have 0 < b - a,       from sub_pos_of_lt h₁,
have 0 < (b - a) * c, from ordered_ring.mul_pos (b - a) c this h₂,
begin
  rw mul_sub_right_distrib at this,
  apply lt_of_sub_pos this
end

instance ordered_ring.to_ordered_semiring [s : ordered_ring α] : ordered_semiring α :=
{ mul_zero                   := mul_zero,
  zero_mul                   := zero_mul,
  add_left_cancel            := @add_left_cancel α _,
  add_right_cancel           := @add_right_cancel α _,
  le_of_add_le_add_left      := @le_of_add_le_add_left α _,
  mul_le_mul_of_nonneg_left  := @ordered_ring.mul_le_mul_of_nonneg_left α _,
  mul_le_mul_of_nonneg_right := @ordered_ring.mul_le_mul_of_nonneg_right α _,
  mul_lt_mul_of_pos_left     := @ordered_ring.mul_lt_mul_of_pos_left α _,
  mul_lt_mul_of_pos_right    := @ordered_ring.mul_lt_mul_of_pos_right α _,
  ..s }

section ordered_ring
variable [ordered_ring α]

lemma mul_le_mul_of_nonpos_left {a b c : α} (h : b ≤ a) (hc : c ≤ 0) : c * a ≤ c * b :=
have -c ≥ 0,              from neg_nonneg_of_nonpos hc,
have -c * b ≤ -c * a,     from mul_le_mul_of_nonneg_left h this,
have -(c * b) ≤ -(c * a), by rwa [← neg_mul_eq_neg_mul, ← neg_mul_eq_neg_mul] at this,
le_of_neg_le_neg this

lemma mul_le_mul_of_nonpos_right {a b c : α} (h : b ≤ a) (hc : c ≤ 0) : a * c ≤ b * c :=
have -c ≥ 0,              from neg_nonneg_of_nonpos hc,
have b * -c ≤ a * -c,     from mul_le_mul_of_nonneg_right h this,
have -(b * c) ≤ -(a * c), by rwa [← neg_mul_eq_mul_neg, ← neg_mul_eq_mul_neg] at this,
le_of_neg_le_neg this

lemma mul_nonneg_of_nonpos_of_nonpos {a b : α} (ha : a ≤ 0) (hb : b ≤ 0) : 0 ≤ a * b :=
have 0 * b ≤ a * b, from mul_le_mul_of_nonpos_right ha hb,
by rwa zero_mul at this

lemma mul_lt_mul_of_neg_left {a b c : α} (h : b < a) (hc : c < 0) : c * a < c * b :=
have -c > 0,              from neg_pos_of_neg hc,
have -c * b < -c * a,     from mul_lt_mul_of_pos_left h this,
have -(c * b) < -(c * a), by rwa [← neg_mul_eq_neg_mul, ← neg_mul_eq_neg_mul] at this,
lt_of_neg_lt_neg this

lemma mul_lt_mul_of_neg_right {a b c : α} (h : b < a) (hc : c < 0) : a * c < b * c :=
have -c > 0,              from neg_pos_of_neg hc,
have b * -c < a * -c,     from mul_lt_mul_of_pos_right h this,
have -(b * c) < -(a * c), by rwa [← neg_mul_eq_mul_neg, ← neg_mul_eq_mul_neg] at this,
lt_of_neg_lt_neg this

lemma mul_pos_of_neg_of_neg {a b : α} (ha : a < 0) (hb : b < 0) : 0 < a * b :=
have 0 * b < a * b, from mul_lt_mul_of_neg_right ha hb,
by rwa zero_mul at this

end ordered_ring

class linear_ordered_ring (α : Type u) extends ordered_ring α, linear_order α :=
(zero_lt_one : zero < one)

instance linear_ordered_ring.to_linear_ordered_semiring [s : linear_ordered_ring α] : linear_ordered_semiring α :=
{ mul_zero                   := mul_zero,
  zero_mul                   := zero_mul,
  add_left_cancel            := @add_left_cancel α _,
  add_right_cancel           := @add_right_cancel α _,
  le_of_add_le_add_left      := @le_of_add_le_add_left α _,
  mul_le_mul_of_nonneg_left  := @mul_le_mul_of_nonneg_left α _,
  mul_le_mul_of_nonneg_right := @mul_le_mul_of_nonneg_right α _,
  mul_lt_mul_of_pos_left     := @mul_lt_mul_of_pos_left α _,
  mul_lt_mul_of_pos_right    := @mul_lt_mul_of_pos_right α _,
  le_total                   := linear_ordered_ring.le_total,
  ..s }

section linear_ordered_ring
variable [linear_ordered_ring α]

lemma mul_self_nonneg (a : α) : a * a ≥ 0 :=
or.elim (le_total 0 a)
  (assume h : a ≥ 0, mul_nonneg h h)
  (assume h : a ≤ 0, mul_nonneg_of_nonpos_of_nonpos h h)

lemma pos_and_pos_or_neg_and_neg_of_mul_pos {a b : α} (hab : a * b > 0) :
    (a > 0 ∧ b > 0) ∨ (a < 0 ∧ b < 0) :=
match lt_trichotomy 0 a with
| or.inl hlt₁          :=
  match lt_trichotomy 0 b with
  | or.inl hlt₂          := or.inl ⟨hlt₁, hlt₂⟩
  | or.inr (or.inl heq₂) := begin rw [← heq₂, mul_zero] at hab, exact absurd hab (lt_irrefl _) end
  | or.inr (or.inr hgt₂) := absurd hab (lt_asymm (mul_neg_of_pos_of_neg hlt₁ hgt₂))
  end
| or.inr (or.inl heq₁) := begin rw [← heq₁, zero_mul] at hab, exact absurd hab (lt_irrefl _) end
| or.inr (or.inr hgt₁) :=
  match lt_trichotomy 0 b with
  | or.inl hlt₂          := absurd hab (lt_asymm (mul_neg_of_neg_of_pos hgt₁ hlt₂))
  | or.inr (or.inl heq₂) := begin rw [← heq₂, mul_zero] at hab, exact absurd hab (lt_irrefl _) end
  | or.inr (or.inr hgt₂) := or.inr ⟨hgt₁, hgt₂⟩
  end
end

lemma gt_of_mul_lt_mul_neg_left {a b c : α} (h : c * a < c * b) (hc : c ≤ 0) : a > b :=
have nhc : -c ≥ 0, from neg_nonneg_of_nonpos hc,
have h2 : -(c * b) < -(c * a), from neg_lt_neg h,
have h3 : (-c) * b < (-c) * a, from calc
     (-c) * b = - (c * b)    : by rewrite neg_mul_eq_neg_mul
          ... < -(c * a)     : h2
          ... = (-c) * a     : by rewrite neg_mul_eq_neg_mul,
lt_of_mul_lt_mul_left h3 nhc


lemma zero_gt_neg_one : -1 < (0:α) :=
begin
  have this := neg_lt_neg (@zero_lt_one α _),
  rwa neg_zero at this
end

lemma le_of_mul_le_of_ge_one {a b c : α} (h : a * c ≤ b) (hb : b ≥ 0) (hc : c ≥ 1) : a ≤ b :=
have h' : a * c ≤ b * c, from calc
     a * c ≤ b : h
       ... = b * 1 : by rewrite mul_one
       ... ≤ b * c : mul_le_mul_of_nonneg_left hc hb,
le_of_mul_le_mul_right h' (lt_of_lt_of_le zero_lt_one hc)

lemma nonneg_le_nonneg_of_squares_le {a b : α} (hb : b ≥ 0) (h : a * a ≤ b * b) : a ≤ b :=
le_of_not_gt (λhab, not_le_of_gt (mul_self_lt_mul_self hb hab) h)

lemma mul_self_le_mul_self_iff {a b : α} (h1 : 0 ≤ a) (h2 : 0 ≤ b) : a ≤ b ↔ a * a ≤ b * b :=
⟨mul_self_le_mul_self h1, nonneg_le_nonneg_of_squares_le h2⟩

lemma mul_self_lt_mul_self_iff {a b : α} (h1 : 0 ≤ a) (h2 : 0 ≤ b) : a < b ↔ a * a < b * b :=
iff.trans (lt_iff_not_ge _ _) $ iff.trans (not_iff_not_of_iff $ mul_self_le_mul_self_iff h2 h1) $
  iff.symm (lt_iff_not_ge _ _)

lemma linear_ordered_ring.eq_zero_or_eq_zero_of_mul_eq_zero
        {a b : α} (h : a * b = 0) : a = 0 ∨ b = 0 :=
match lt_trichotomy 0 a with
| or.inl hlt₁          :=
  match lt_trichotomy 0 b with
  | or.inl hlt₂          :=
    have 0 < a * b, from mul_pos hlt₁ hlt₂,
    begin rw h at this, exact absurd this (lt_irrefl _) end
  | or.inr (or.inl heq₂) := or.inr heq₂.symm
  | or.inr (or.inr hgt₂) :=
    have 0 > a * b, from mul_neg_of_pos_of_neg hlt₁ hgt₂,
    begin rw h at this, exact absurd this (lt_irrefl _)  end
  end
| or.inr (or.inl heq₁) := or.inl heq₁.symm
| or.inr (or.inr hgt₁) :=
  match lt_trichotomy 0 b with
  | or.inl hlt₂          :=
    have 0 > a * b, from mul_neg_of_neg_of_pos hgt₁ hlt₂,
    begin rw h at this, exact absurd this (lt_irrefl _)  end
  | or.inr (or.inl heq₂) := or.inr heq₂.symm
  | or.inr (or.inr hgt₂) :=
    have 0 < a * b, from mul_pos_of_neg_of_neg hgt₁ hgt₂,
    begin rw h at this, exact absurd this (lt_irrefl _)  end
  end
end

end linear_ordered_ring

class linear_ordered_comm_ring (α : Type u) extends linear_ordered_ring α, comm_monoid α

instance linear_ordered_comm_ring.to_integral_domain [s: linear_ordered_comm_ring α] : integral_domain α :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := @linear_ordered_ring.eq_zero_or_eq_zero_of_mul_eq_zero α _,
  ..s }

class decidable_linear_ordered_comm_ring (α : Type u) extends linear_ordered_comm_ring α,
    decidable_linear_ordered_comm_group α

instance decidable_linear_ordered_comm_ring.to_decidable_linear_ordered_semiring [d : decidable_linear_ordered_comm_ring α] :
   decidable_linear_ordered_semiring α :=
let s : linear_ordered_semiring α := @linear_ordered_ring.to_linear_ordered_semiring α _ in
{ zero_mul                   := @linear_ordered_semiring.zero_mul α s,
  mul_zero                   := @linear_ordered_semiring.mul_zero α s,
  add_left_cancel            := @linear_ordered_semiring.add_left_cancel α s,
  add_right_cancel           := @linear_ordered_semiring.add_right_cancel α s,
  le_of_add_le_add_left      := @linear_ordered_semiring.le_of_add_le_add_left α s,
  mul_le_mul_of_nonneg_left  := @linear_ordered_semiring.mul_le_mul_of_nonneg_left α s,
  mul_le_mul_of_nonneg_right := @linear_ordered_semiring.mul_le_mul_of_nonneg_right α s,
  mul_lt_mul_of_pos_left     := @linear_ordered_semiring.mul_lt_mul_of_pos_left α s,
  mul_lt_mul_of_pos_right    := @linear_ordered_semiring.mul_lt_mul_of_pos_right α s,
  ..d }
