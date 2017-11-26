/-
Copyright (c) 2014 Robert Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Lewis, Leonardo de Moura
-/
prelude
import init.algebra.ordered_ring init.algebra.field

set_option old_structure_cmd true

universe u

class linear_ordered_field (α : Type u) extends linear_ordered_ring α, field α

section linear_ordered_field
variables {α : Type u} [linear_ordered_field α]

lemma mul_zero_lt_mul_inv_of_pos {a : α} (h : 0 < a) : a * 0 < a * (1 / a) :=
calc a * 0 = 0           : by rw mul_zero
       ... < 1           : zero_lt_one
       ... = a * a⁻¹     : eq.symm (mul_inv_cancel (ne.symm (ne_of_lt h)))
       ... = a * (1 / a) : by rw inv_eq_one_div

lemma mul_zero_lt_mul_inv_of_neg {a : α} (h : a < 0) : a * 0 < a * (1 / a) :=
calc  a * 0 = 0           : by rw mul_zero
        ... < 1           : zero_lt_one
        ... = a * a⁻¹     : eq.symm (mul_inv_cancel (ne_of_lt h))
        ... = a * (1 / a) : by rw inv_eq_one_div

lemma one_div_pos_of_pos {a : α} (h : 0 < a) : 0 < 1 / a :=
lt_of_mul_lt_mul_left (mul_zero_lt_mul_inv_of_pos h) (le_of_lt h)

lemma one_div_neg_of_neg {a : α} (h : a < 0) : 1 / a < 0 :=
gt_of_mul_lt_mul_neg_left (mul_zero_lt_mul_inv_of_neg h) (le_of_lt h)

lemma le_mul_of_ge_one_right {a b : α} (hb : b ≥ 0) (h : a ≥ 1) : b ≤ b * a :=
suffices b * 1 ≤ b * a, by rwa mul_one at this,
mul_le_mul_of_nonneg_left h hb

lemma le_mul_of_ge_one_left {a b : α} (hb : b ≥ 0) (h : a ≥ 1) : b ≤ a * b :=
by rw mul_comm; exact le_mul_of_ge_one_right hb h

lemma lt_mul_of_gt_one_right {a b : α} (hb : b > 0) (h : a > 1) : b < b * a :=
suffices b * 1 < b * a, by rwa mul_one at this,
mul_lt_mul_of_pos_left h hb

lemma one_le_div_of_le (a : α) {b : α} (hb : b > 0) (h : b ≤ a) : 1 ≤ a / b :=
have hb'   : b ≠ 0,     from ne.symm (ne_of_lt hb),
have hbinv : 1 / b > 0, from  one_div_pos_of_pos hb,
calc
   1  = b * (1 / b)  : eq.symm (mul_one_div_cancel hb')
   ... ≤ a * (1 / b) : mul_le_mul_of_nonneg_right h (le_of_lt hbinv)
   ... = a / b       : eq.symm $ div_eq_mul_one_div a b

lemma le_of_one_le_div (a : α) {b : α} (hb : b > 0) (h : 1 ≤ a / b) : b ≤ a :=
have hb'   : b ≠ 0,     from ne.symm (ne_of_lt hb),
calc
   b   ≤ b * (a / b) : le_mul_of_ge_one_right (le_of_lt hb) h
   ... = a           : by rw [mul_div_cancel' _ hb']

lemma one_lt_div_of_lt (a : α) {b : α} (hb : b > 0) (h : b < a) : 1 < a / b :=
have hb' : b ≠ 0, from ne.symm (ne_of_lt hb),
have hbinv : 1 / b > 0, from  one_div_pos_of_pos hb, calc
     1 = b * (1 / b) : eq.symm (mul_one_div_cancel hb')
   ... < a * (1 / b) : mul_lt_mul_of_pos_right h hbinv
   ... = a / b       : eq.symm $ div_eq_mul_one_div a b

lemma lt_of_one_lt_div (a : α) {b : α} (hb : b > 0) (h : 1 < a / b) : b < a :=
have hb' : b ≠ 0, from ne.symm (ne_of_lt hb),
calc
   b   < b * (a / b) : lt_mul_of_gt_one_right hb h
   ... = a           : by rw [mul_div_cancel' _ hb']

-- the following lemmas amount to four iffs, for <, ≤, ≥, >.

lemma mul_le_of_le_div {a b c : α} (hc : 0 < c) (h : a ≤ b / c) : a * c ≤ b :=
div_mul_cancel b (ne.symm (ne_of_lt hc)) ▸ mul_le_mul_of_nonneg_right h (le_of_lt hc)

lemma le_div_of_mul_le {a b c : α} (hc : 0 < c) (h : a * c ≤ b) : a ≤ b / c :=
calc
    a   = a * c * (1 / c) : mul_mul_div a (ne.symm (ne_of_lt hc))
    ... ≤ b * (1 / c)     : mul_le_mul_of_nonneg_right h (le_of_lt (one_div_pos_of_pos hc))
    ... = b / c           : eq.symm $ div_eq_mul_one_div b c

lemma mul_lt_of_lt_div {a b c : α} (hc : 0 < c) (h : a < b / c) : a * c < b :=
div_mul_cancel b (ne.symm (ne_of_lt hc)) ▸ mul_lt_mul_of_pos_right h hc

lemma lt_div_of_mul_lt {a b c : α} (hc : 0 < c) (h : a * c < b) : a < b / c :=
calc
   a   = a * c * (1 / c) : mul_mul_div a (ne.symm (ne_of_lt hc))
   ... < b * (1 / c)     : mul_lt_mul_of_pos_right h (one_div_pos_of_pos hc)
   ... = b / c           : eq.symm $ div_eq_mul_one_div b c

lemma mul_le_of_div_le_of_neg {a b c : α} (hc : c < 0) (h : b / c ≤ a) : a * c ≤ b :=
div_mul_cancel b (ne_of_lt hc) ▸ mul_le_mul_of_nonpos_right h (le_of_lt hc)

lemma div_le_of_mul_le_of_neg {a b c : α} (hc : c < 0) (h : a * c ≤ b) : b / c ≤ a :=
calc
   a   = a * c * (1 / c) : mul_mul_div a (ne_of_lt hc)
    ... ≥ b * (1 / c)     : mul_le_mul_of_nonpos_right h (le_of_lt (one_div_neg_of_neg hc))
    ... = b / c           : eq.symm $ div_eq_mul_one_div b c

lemma mul_lt_of_gt_div_of_neg {a b c : α} (hc : c < 0) (h : a > b / c) : a * c < b :=
div_mul_cancel b (ne_of_lt hc) ▸ mul_lt_mul_of_neg_right h hc

lemma div_lt_of_mul_lt_of_pos {a b c : α} (hc : c > 0) (h : b < a * c) : b / c < a :=
calc
   a   = a * c * (1 / c) : mul_mul_div a (ne_of_gt hc)
   ... > b * (1 / c)     : mul_lt_mul_of_pos_right h (one_div_pos_of_pos hc)
   ... = b / c           : eq.symm $ div_eq_mul_one_div b c

lemma div_lt_of_mul_gt_of_neg {a b c : α} (hc : c < 0) (h : a * c < b) : b / c < a :=
calc
   a   = a * c * (1 / c) : mul_mul_div a (ne_of_lt hc)
   ... > b * (1 / c)     : mul_lt_mul_of_neg_right h (one_div_neg_of_neg hc)
   ... = b / c           : eq.symm $ div_eq_mul_one_div b c

lemma div_le_of_le_mul {a b c : α} (hb : b > 0) (h : a ≤ b * c) : a / b ≤ c :=
calc
   a / b = a * (1 / b)       : div_eq_mul_one_div a b
     ... ≤ (b * c) * (1 / b) : mul_le_mul_of_nonneg_right h (le_of_lt (one_div_pos_of_pos hb))
     ... = (b * c) / b       : eq.symm $ div_eq_mul_one_div (b * c) b
     ... = c                 : by rw [mul_div_cancel_left _ (ne.symm (ne_of_lt hb))]

lemma le_mul_of_div_le {a b c : α} (hc : c > 0) (h : a / c ≤ b) : a ≤ b * c :=
calc
   a = a / c * c : by rw (div_mul_cancel _ (ne.symm (ne_of_lt hc)))
 ... ≤ b * c     : mul_le_mul_of_nonneg_right h (le_of_lt hc)

  -- following these in the isabelle file, there are 8 biconditionals for the above with - signs
  -- skipping for now

lemma mul_sub_mul_div_mul_neg {a b c d : α} (hc : c ≠ 0) (hd : d ≠ 0) (h : a / c < b / d) :
      (a * d - b * c) / (c * d) < 0 :=
have h1 : a / c - b / d < 0, from calc
  a / c - b / d < b / d - b / d : sub_lt_sub_right h _
            ... = 0             : by rw sub_self,
calc
    0 > a / c - b / d             : h1
  ... = (a * d - c * b) / (c * d) : div_sub_div _ _ hc hd
  ... = (a * d - b * c) / (c * d) : by rw (mul_comm b c)

lemma mul_sub_mul_div_mul_nonpos {a b c d : α} (hc : c ≠ 0) (hd : d ≠ 0) (h : a / c ≤ b / d) :
      (a * d - b * c) / (c * d) ≤ 0 :=
have h1 : a / c - b / d ≤ 0, from calc
    a / c - b / d ≤ b / d - b / d : sub_le_sub_right h _
              ... = 0             : by rw sub_self,
calc
    0 ≥ a / c - b / d : h1
  ... = (a * d - c * b) / (c * d) : div_sub_div _ _ hc hd
  ... = (a * d - b * c) / (c * d) : by rw (mul_comm b c)

lemma div_lt_div_of_mul_sub_mul_div_neg {a b c d : α} (hc : c ≠ 0) (hd : d ≠ 0)
      (h : (a * d - b * c) / (c * d) < 0) : a / c < b / d :=
have (a * d - c * b) / (c * d) < 0,     by rwa [mul_comm c b],
have a / c - b / d < 0,                 by rwa [div_sub_div _ _ hc hd],
have a / c - b / d + b / d < 0 + b / d, from add_lt_add_right this _,
by rwa [zero_add, sub_eq_add_neg, neg_add_cancel_right] at this


lemma div_le_div_of_mul_sub_mul_div_nonpos {a b c d : α} (hc : c ≠ 0) (hd : d ≠ 0)
      (h : (a * d - b * c) / (c * d) ≤ 0) : a / c ≤ b / d :=
have (a * d - c * b) / (c * d) ≤ 0,     by rwa [mul_comm c b],
have a / c - b / d ≤ 0,                 by rwa [div_sub_div _ _ hc hd],
have a / c - b / d + b / d ≤ 0 + b / d, from add_le_add_right this _,
by rwa [zero_add, sub_eq_add_neg, neg_add_cancel_right] at this


lemma div_pos_of_pos_of_pos {a b : α} : 0 < a → 0 < b → 0 < a / b :=
begin
  intros,
  rw div_eq_mul_one_div,
  apply mul_pos,
  assumption,
  apply one_div_pos_of_pos,
  assumption
end

lemma div_nonneg_of_nonneg_of_pos {a b : α} : 0 ≤ a → 0 < b → 0 ≤ a / b :=
begin
  intros, rw div_eq_mul_one_div,
  apply mul_nonneg, assumption,
  apply le_of_lt,
  apply one_div_pos_of_pos,
  assumption
end

lemma div_neg_of_neg_of_pos {a b : α} : a < 0 → 0 < b → a / b < 0 :=
begin
  intros, rw div_eq_mul_one_div,
  apply mul_neg_of_neg_of_pos,
  assumption,
  apply one_div_pos_of_pos,
  assumption
end

lemma div_nonpos_of_nonpos_of_pos {a b : α} : a ≤ 0 → 0 < b → a / b ≤ 0 :=
begin
  intros, rw div_eq_mul_one_div,
  apply mul_nonpos_of_nonpos_of_nonneg,
  assumption,
  apply le_of_lt,
  apply one_div_pos_of_pos,
  assumption
end

lemma div_neg_of_pos_of_neg {a b : α} : 0 < a → b < 0 → a / b < 0 :=
begin
  intros, rw div_eq_mul_one_div,
  apply mul_neg_of_pos_of_neg,
  assumption,
  apply one_div_neg_of_neg,
  assumption
end

lemma div_nonpos_of_nonneg_of_neg {a b : α} : 0 ≤ a → b < 0 → a / b ≤ 0 :=
begin
  intros, rw div_eq_mul_one_div,
  apply mul_nonpos_of_nonneg_of_nonpos,
  assumption,
  apply le_of_lt,
  apply one_div_neg_of_neg,
  assumption
end

lemma div_pos_of_neg_of_neg {a b : α} : a < 0 → b < 0 → 0 < a / b :=
begin
  intros, rw div_eq_mul_one_div,
  apply mul_pos_of_neg_of_neg,
  assumption,
  apply one_div_neg_of_neg,
  assumption
end

lemma div_nonneg_of_nonpos_of_neg {a b : α} : a ≤ 0 → b < 0 → 0 ≤ a / b :=
begin
  intros, rw div_eq_mul_one_div,
  apply mul_nonneg_of_nonpos_of_nonpos,
  assumption,
  apply le_of_lt,
  apply one_div_neg_of_neg,
  assumption
end

lemma div_lt_div_of_lt_of_pos {a b c : α} (h : a < b) (hc : 0 < c) : a / c < b / c :=
begin
  intros,
  rw [div_eq_mul_one_div a c, div_eq_mul_one_div b c],
  exact mul_lt_mul_of_pos_right h (one_div_pos_of_pos hc)
end

lemma div_le_div_of_le_of_pos {a b c : α} (h : a ≤ b) (hc : 0 < c) : a / c ≤ b / c :=
begin
  rw [div_eq_mul_one_div a c, div_eq_mul_one_div b c],
  exact mul_le_mul_of_nonneg_right h (le_of_lt (one_div_pos_of_pos hc))
end

lemma div_lt_div_of_lt_of_neg {a b c : α} (h : b < a) (hc : c < 0) : a / c < b / c :=
begin
  rw [div_eq_mul_one_div a c, div_eq_mul_one_div b c],
  exact mul_lt_mul_of_neg_right h (one_div_neg_of_neg hc)
end

lemma div_le_div_of_le_of_neg {a b c : α} (h : b ≤ a) (hc : c < 0) : a / c ≤ b / c :=
begin
  rw [div_eq_mul_one_div a c, div_eq_mul_one_div b c],
  exact mul_le_mul_of_nonpos_right h (le_of_lt (one_div_neg_of_neg hc))
end

lemma two_pos : (2:α) > 0 :=
begin unfold bit0, exact add_pos zero_lt_one zero_lt_one end

lemma two_ne_zero : (2:α) ≠ 0 :=
ne.symm (ne_of_lt two_pos)

lemma add_halves (a : α) : a / 2 + a / 2 = a :=
calc
   a / 2 + a / 2 = (a + a) / 2 : by rw div_add_div_same
    ... = (a * 1 + a * 1) / 2   : by rw mul_one
    ... = (a * (1 + 1)) / 2     : by rw left_distrib
    ... = (a * 2) / 2           : by rw one_add_one_eq_two
    ... = a                     : by rw [@mul_div_cancel α _ _ _ two_ne_zero]

lemma sub_self_div_two (a : α) : a - a / 2 = a / 2 :=
suffices a / 2 + a / 2 - a / 2 = a / 2, by rwa add_halves at this,
by rw [add_sub_cancel]

lemma add_midpoint {a b : α} (h : a < b) : a + (b - a) / 2 < b :=
begin
  rw [← div_sub_div_same, sub_eq_add_neg, add_comm (b/2), ← add_assoc, ← sub_eq_add_neg],
  apply add_lt_of_lt_sub_right,
  rw [sub_self_div_two, sub_self_div_two],
  apply div_lt_div_of_lt_of_pos h two_pos
end

lemma div_two_sub_self (a : α) : a / 2 - a = - (a / 2) :=
suffices a / 2 - (a / 2 + a / 2) = - (a / 2), by rwa add_halves at this,
by rw [sub_add_eq_sub_sub, sub_self, zero_sub]

lemma add_self_div_two (a : α) : (a + a) / 2 = a :=
eq.symm
  (iff.mpr (eq_div_iff_mul_eq _ _ (ne_of_gt (add_pos (@zero_lt_one α _) zero_lt_one)))
           (begin unfold bit0, rw [left_distrib, mul_one] end))

lemma two_gt_one : (2:α) > 1 :=
calc (2:α) = 1+1 : one_add_one_eq_two
     ...   > 1+0 : add_lt_add_left zero_lt_one _
     ...   = 1   : add_zero 1

lemma two_ge_one : (2:α) ≥ 1 :=
le_of_lt two_gt_one

lemma four_pos : (4:α) > 0 :=
add_pos two_pos two_pos

lemma mul_le_mul_of_mul_div_le {a b c d : α} (h : a * (b / c) ≤ d) (hc : c > 0) : b * a ≤ d * c :=
begin
  rw [← mul_div_assoc] at h, rw [mul_comm b],
  apply le_mul_of_div_le hc h
end

lemma div_two_lt_of_pos {a : α} (h : a > 0) : a / 2 < a :=
suffices a / (1 + 1) < a, begin unfold bit0, assumption end,
have ha : a / 2 > 0, from div_pos_of_pos_of_pos h (add_pos zero_lt_one zero_lt_one),
calc
      a / 2 < a / 2 + a / 2 : lt_add_of_pos_left _ ha
        ... = a             : add_halves a

lemma div_mul_le_div_mul_of_div_le_div_pos {a b c d e : α} (hb : b ≠ 0) (hd : d ≠ 0) (h : a / b ≤ c / d)
      (he : e > 0) : a / (b * e) ≤ c / (d * e) :=
begin
  have h₁ := field.div_mul_eq_div_mul_one_div a hb (ne_of_gt he),
  have h₂ := field.div_mul_eq_div_mul_one_div c hd (ne_of_gt he),
  rw [h₁, h₂],
  apply mul_le_mul_of_nonneg_right h,
  apply le_of_lt,
  apply one_div_pos_of_pos he
end

lemma exists_add_lt_and_pos_of_lt {a b : α} (h : b < a) : ∃ c : α, b + c < a ∧ c > 0 :=
begin
  apply exists.intro ((a - b) / (1 + 1)),
  split,
  {have h2 : a + a > (b + b) + (a - b),
    calc
      a + a > b + a             : add_lt_add_right h _
        ... = b + a + b - b     : by rw add_sub_cancel
        ... = b + b + a - b     : by simp
        ... = (b + b) + (a - b) : by rw add_sub,
   have h3 : (a + a) / 2 > ((b + b) + (a - b)) / 2,
     exact div_lt_div_of_lt_of_pos h2 two_pos,
   rw [one_add_one_eq_two, sub_eq_add_neg],
   rw [add_self_div_two, ← div_add_div_same, add_self_div_two, sub_eq_add_neg] at h3,
   exact h3},
  exact div_pos_of_pos_of_pos (sub_pos_of_lt h) two_pos
end

lemma ge_of_forall_ge_sub {a b : α} (h : ∀ ε : α, ε > 0 → a ≥ b - ε) : a ≥ b :=
begin
  apply le_of_not_gt,
  intro hb,
  cases exists_add_lt_and_pos_of_lt hb with c hc,
  have  hc' := h c (and.right hc),
  apply (not_le_of_gt (and.left hc)) (le_add_of_sub_right_le hc')
end

lemma one_div_lt_one_div_of_lt {a b : α} (ha : 0 < a) (h : a < b) : 1 / b < 1 / a :=
begin
  apply lt_div_of_mul_lt ha,
  rw [mul_comm, ← div_eq_mul_one_div],
  apply div_lt_of_mul_lt_of_pos (lt_trans ha h),
  rwa [one_mul]
end

lemma one_div_le_one_div_of_le {a b : α} (ha : 0 < a) (h : a ≤ b) : 1 / b ≤ 1 / a :=
(lt_or_eq_of_le h).elim
  (λ h, le_of_lt $ one_div_lt_one_div_of_lt ha h)
  (λ h, by rw [h])

lemma one_div_lt_one_div_of_lt_of_neg {a b : α} (hb : b < 0) (h : a < b) : 1 / b < 1 / a :=
begin
  apply div_lt_of_mul_gt_of_neg hb,
  rw [mul_comm, ← div_eq_mul_one_div],
  apply div_lt_of_mul_gt_of_neg (lt_trans h hb),
  rwa [one_mul]
end

lemma one_div_le_one_div_of_le_of_neg {a b : α} (hb : b < 0) (h : a ≤ b) : 1 / b ≤ 1 / a :=
(lt_or_eq_of_le h).elim
  (λ h, le_of_lt $ one_div_lt_one_div_of_lt_of_neg hb h)
  (λ h, by rw [h])

lemma le_of_one_div_le_one_div {a b : α} (h : 0 < a) (hl : 1 / a ≤ 1 / b) : b ≤ a :=
le_of_not_gt $ λ hn, not_lt_of_ge hl $ one_div_lt_one_div_of_lt h hn

lemma le_of_one_div_le_one_div_of_neg {a b : α} (h : b < 0) (hl : 1 / a ≤ 1 / b) : b ≤ a :=
le_of_not_gt $ λ hn, not_lt_of_ge hl $ one_div_lt_one_div_of_lt_of_neg h hn

lemma lt_of_one_div_lt_one_div {a b : α} (h : 0 < a) (hl : 1 / a < 1 / b) : b < a :=
lt_of_not_ge $ λ hn, not_le_of_gt hl $ one_div_le_one_div_of_le h hn

lemma lt_of_one_div_lt_one_div_of_neg {a b : α} (h : b < 0) (hl : 1 / a < 1 / b) : b < a :=
lt_of_not_ge $ λ hn, not_le_of_gt hl $ one_div_le_one_div_of_le_of_neg h hn

lemma one_div_le_of_one_div_le_of_pos {a b : α} (ha : a > 0) (h : 1 / a ≤ b) : 1 / b ≤ a :=
begin
  rw [← division_ring.one_div_one_div (ne_of_gt ha)],
  apply one_div_le_one_div_of_le _ h,
  apply one_div_pos_of_pos ha
end

lemma one_div_le_of_one_div_le_of_neg {a b : α} (hb : b < 0) (h : 1 / a ≤ b) : 1 / b ≤ a :=
le_of_not_gt $ λ hl, begin
  have : a < 0, from lt_trans hl (one_div_neg_of_neg hb),
  rw ← division_ring.one_div_one_div (ne_of_lt this) at hl,
  exact not_lt_of_ge h (lt_of_one_div_lt_one_div_of_neg hb hl)
end

lemma one_lt_one_div {a : α} (h1 : 0 < a) (h2 : a < 1) : 1 < 1 / a :=
suffices 1 / 1 < 1 / a, by rwa one_div_one at this,
one_div_lt_one_div_of_lt h1 h2

lemma one_le_one_div {a : α} (h1 : 0 < a) (h2 : a ≤ 1) : 1 ≤ 1 / a :=
suffices 1 / 1 ≤ 1 / a, by rwa one_div_one at this,
one_div_le_one_div_of_le h1 h2

lemma one_div_lt_neg_one {a : α} (h1 : a < 0) (h2 : -1 < a) : 1 / a < -1 :=
suffices 1 / a < 1 / -1, by rwa one_div_neg_one_eq_neg_one at this,
one_div_lt_one_div_of_lt_of_neg h1 h2

lemma one_div_le_neg_one {a : α} (h1 : a < 0) (h2 : -1 ≤ a) : 1 / a ≤ -1 :=
suffices 1 / a ≤ 1 / -1, by rwa one_div_neg_one_eq_neg_one at this,
one_div_le_one_div_of_le_of_neg h1 h2

lemma div_lt_div_of_pos_of_lt_of_pos {a b c : α} (hb : 0 < b) (h : b < a) (hc : 0 < c) : c / a < c / b :=
begin
  apply lt_of_sub_neg,
  rw [div_eq_mul_one_div, div_eq_mul_one_div c b, ← mul_sub_left_distrib],
  apply mul_neg_of_pos_of_neg,
  exact hc,
  apply sub_neg_of_lt,
  apply one_div_lt_one_div_of_lt; assumption,
end

end linear_ordered_field

class discrete_linear_ordered_field (α : Type u) extends linear_ordered_field α,
      decidable_linear_ordered_comm_ring α :=
(inv_zero : inv zero = zero)

section discrete_linear_ordered_field
variables {α : Type u}

instance discrete_linear_ordered_field.to_discrete_field [s : discrete_linear_ordered_field α] : discrete_field α :=
{ has_decidable_eq := @decidable_linear_ordered_comm_ring.decidable_eq α (@discrete_linear_ordered_field.to_decidable_linear_ordered_comm_ring α s),
  ..s }

variables [discrete_linear_ordered_field α]

lemma pos_of_one_div_pos {a : α} (h : 0 < 1 / a) : 0 < a :=
 have h1 : 0 < 1 / (1 / a), from one_div_pos_of_pos h,
 have h2 : 1 / a ≠ 0, from
   (assume h3 : 1 / a = 0,
    have h4 : 1 / (1 / a) = 0, from eq.symm h3 ▸ div_zero 1,
    absurd h4 (ne.symm (ne_of_lt h1))),
 (division_ring.one_div_one_div (ne_zero_of_one_div_ne_zero h2)) ▸ h1

lemma neg_of_one_div_neg {a : α} (h : 1 / a < 0) : a < 0 :=
have h1 : 0 < - (1 / a), from neg_pos_of_neg h,
have ha : a ≠ 0, from ne_zero_of_one_div_ne_zero (ne_of_lt h),
have h2 : 0 < 1 / (-a), from eq.symm (division_ring.one_div_neg_eq_neg_one_div ha) ▸ h1,
have h3 : 0 < -a, from pos_of_one_div_pos h2,
neg_of_neg_pos h3

lemma div_mul_le_div_mul_of_div_le_div_pos' {a b c d e : α} (h : a / b ≤ c / d)
          (he : e > 0) : a / (b * e) ≤ c / (d * e) :=
begin
  rw [div_mul_eq_div_mul_one_div, div_mul_eq_div_mul_one_div],
  apply mul_le_mul_of_nonneg_right h,
  apply le_of_lt,
  apply one_div_pos_of_pos he
end

end discrete_linear_ordered_field
