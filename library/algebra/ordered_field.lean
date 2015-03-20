/-
Copyright (c) 2014 Robert Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: algebra.ordered_field
Authors: Robert Lewis

-/

import algebra.ordered_ring algebra.field
open eq eq.ops

namespace algebra
          
structure linear_ordered_field [class] (A : Type) extends linear_ordered_ring A, field A

section linear_ordered_field
  
  variable {A : Type}
  variables [s : linear_ordered_field A] {a b c : A}
  include s
  
  -- ordered ring theorem?
  -- split H3 into its own lemma
  theorem gt_of_mul_lt_mul_neg_left (H : c * a < c * b) (Hc : c ≤ 0) : a > b :=
    have nhc : -c ≥ 0, from neg_nonneg_of_nonpos Hc,
    have H2 : -(c * b) < -(c * a), from iff.mp' (neg_lt_neg_iff_lt _ _) H,
    have H3 : (-c) * b < (-c) * a, from calc
      (-c) * b = - (c * b)    : neg_mul_eq_neg_mul
           ... < -(c * a)     : H2
           ... = (-c) * a     : neg_mul_eq_neg_mul,
    lt_of_mul_lt_mul_left H3 nhc

  -- helpers for following
  theorem mul_zero_lt_mul_inv_of_pos (H : 0 < a) : a * 0 < a * (1 / a) :=
   calc
      a * 0 = 0           : mul_zero
        ... < 1           : zero_lt_one
        ... = a * a⁻¹     : mul_inv_cancel (ne.symm (ne_of_lt H))
        ... = a * (1 / a) : inv_eq_one_div
 
  theorem mul_zero_lt_mul_inv_of_neg (H : a < 0) : a * 0 < a * (1 / a) :=
    calc
      a * 0 = 0           : mul_zero
        ... < 1           : zero_lt_one
        ... = a * a⁻¹     : mul_inv_cancel (ne_of_lt H)
        ... = a * (1 / a) : inv_eq_one_div
  
  theorem div_pos_of_pos (H : 0 < a) : 0 < 1 / a :=
    lt_of_mul_lt_mul_left (mul_zero_lt_mul_inv_of_pos H) (le_of_lt H)

  theorem pos_of_div_pos (H : 0 < 1 / a) : 0 < a :=
    have H1 : 0 < 1 / (1 / a), from div_pos_of_pos H,
    have H2 : 1 / a ≠ 0, from 
      (assume H3 : 1 / a = 0,
      have H4 : 1 / (1 / a) = 0, from H3⁻¹ ▸ div_zero,
      absurd H4 (ne.symm (ne_of_lt H1))),
    (div_div (ne_zero_of_one_div_ne_zero H2)) ▸ H1

  theorem div_neg_of_neg (H : a < 0) : 1 / a < 0 :=
    gt_of_mul_lt_mul_neg_left (mul_zero_lt_mul_inv_of_neg H) (le_of_lt H)

  theorem neg_of_div_neg (H : 1 / a < 0) : a < 0 :=
    have H1 : 0 < - (1 / a), from neg_pos_of_neg H, 
    have Ha : a ≠ 0, from ne_zero_of_one_div_ne_zero (ne_of_lt H),
    have H2 : 0 < 1 / (-a), from (one_div_neg_eq_neg_one_div Ha)⁻¹ ▸ H1,
    have H3 : 0 < -a, from pos_of_div_pos H2,
    neg_of_neg_pos H3

  theorem le_mul_of_ge_one_right (Hb : b ≥ 0) (H : a ≥ 1) : b ≤ b * a :=
      mul_one _ ▸ (mul_le_mul_of_nonneg_left H Hb)

  theorem lt_mul_of_gt_one_right (Hb : b > 0) (H : a > 1) : b < b * a :=
      mul_one _ ▸ (mul_lt_mul_of_pos_left H Hb)

  theorem one_le_div_iff_le (Hb : b > 0) : 1 ≤ a / b ↔ b ≤ a := 
    have Hb' : b ≠ 0, from ne.symm (ne_of_lt Hb),
    iff.intro
    (assume H : 1 ≤ a / b,
      calc
        b   = b           : refl
        ... ≤ b * (a / b) : le_mul_of_ge_one_right (le_of_lt Hb) H
        ... = a           : mul_div_cancel' Hb')
    (assume H : b ≤ a,
      have Hbinv : 1 / b > 0, from  div_pos_of_pos Hb, calc
        1  = b * (1 / b) : mul_one_div_cancel Hb'
       ... ≤ a * (1 / b) : mul_le_mul_of_nonneg_right H (le_of_lt Hbinv)
       ... = a / b       : div_eq_mul_one_div)

  theorem le_of_one_le_div (Hb : b > 0) (H : 1 ≤ a / b) : b ≤ a :=
    (iff.mp (one_le_div_iff_le Hb)) H

  theorem one_le_div_of_le (Hb : b > 0) (H : b ≤ a) : 1 ≤ a / b :=
    (iff.mp' (one_le_div_iff_le Hb)) H

  theorem one_lt_div_iff_lt (Hb : b > 0) : 1 < a / b ↔ b < a :=
    have Hb' : b ≠ 0, from ne.symm (ne_of_lt Hb),
    iff.intro
    (assume H : 1 < a / b,
      calc
        b   = b           : refl
        ... < b * (a / b) : lt_mul_of_gt_one_right Hb H
        ... = a           : mul_div_cancel' Hb')
    (assume H : b < a,
      have Hbinv : 1 / b > 0, from  div_pos_of_pos Hb, calc
        1 = b * (1 / b) : mul_one_div_cancel Hb'
      ... < a * (1 / b) : mul_lt_mul_of_pos_right H Hbinv
      ... = a / b       : div_eq_mul_one_div)

  theorem lt_of_one_lt_div (Hb : b > 0) (H : 1 < a / b) : b < a :=
    (iff.mp (one_lt_div_iff_lt Hb)) H

  theorem one_lt_div_of_lt (Hb : b > 0) (H : b < a) : 1 < a / b :=
    (iff.mp' (one_lt_div_iff_lt Hb)) H

-- why is mul_le_mul under ordered_ring namespace?
  theorem le_of_div_le (H : 0 < a) (Hl : 1 / a ≤ 1 / b) : b ≤ a :=
    have Hb : 0 < b, from pos_of_div_pos (calc
      0   < 1 / a : div_pos_of_pos H
      ... ≤ 1 / b : Hl),
    have H' : 1 ≤ a / b, from (calc
      1   = a / a       : div_self (ne.symm (ne_of_lt H))
      ... = a * (1 / a) :  div_eq_mul_one_div
      ... ≤ a * (1 / b) : ordered_ring.mul_le_mul_of_nonneg_left Hl (le_of_lt H)
      ... = a / b       : div_eq_mul_one_div
      ), le_of_one_le_div Hb H' 
      

  theorem lt_of_div_lt (H : 0 < a) (Hl : 1 / a < 1 / b) : b < a :=
    have Hb : 0 < b, from pos_of_div_pos (calc
      0   < 1 / a : div_pos_of_pos H
      ... < 1 / b : Hl),
    have H : 1 < a / b, from (calc
      1   = a / a       : div_self (ne.symm (ne_of_lt H))
      ... = a * (1 / a) :  div_eq_mul_one_div
      ... < a * (1 / b) : mul_lt_mul_of_pos_left Hl H
      ... = a / b       : div_eq_mul_one_div),
      lt_of_one_lt_div Hb H

  theorem le_of_div_le_neg (H : b < 0) (Hl : 1 / a ≤ 1 / b) : b ≤ a :=
    have Ha : a ≠ 0, from ne_of_lt (neg_of_div_neg (calc
      1 / a ≤ 1 / b : Hl
        ... < 0     : div_neg_of_neg H)),
    have H'   : -b > 0,                from neg_pos_of_neg H,
    have Hl'  : - (1 / b) ≤ - (1 / a), from neg_le_neg Hl,
    have Hl'' : 1 / - b ≤ 1 / - a,     from calc
      1 / -b = - (1 / b) : one_div_neg_eq_neg_one_div (ne_of_lt H)
         ... ≤ - (1 / a) : Hl'
         ... = 1 / -a    : one_div_neg_eq_neg_one_div Ha,
    le_of_neg_le_neg (le_of_div_le H' Hl'')

  theorem lt_of_div_lt_neg (H : b < 0) (Hl : 1 / a < 1 / b) : b < a :=
    have H1 : b ≤ a, from le_of_div_le_neg H (le_of_lt Hl),
    have Hn : b ≠ a, from
      (assume Hn' : b = a,
      have Hl' : 1 / a = 1 / b, from Hn' ▸ refl _, 
      absurd Hl' (ne_of_lt Hl)),
    lt_of_le_of_ne H1 Hn

  theorem div_lt_div_of_lt (Ha : 0 < a) (H : a < b) : 1 / b < 1 / a := 
    lt_of_not_le
      (assume H',
      absurd H (not_lt_of_le (le_of_div_le Ha H'))) 

  theorem div_le_div_of_le (Ha : 0 < a) (H : a ≤ b) : 1 / b ≤ 1 / a := 
    le_of_not_lt
      (assume H',
      absurd H (not_le_of_lt (lt_of_div_lt Ha H')))

  theorem div_lt_div_of_lt_neg (Hb : b < 0) (H : a < b) : 1 / b < 1 / a :=
    lt_of_not_le
      (assume H',
      absurd H (not_lt_of_le (le_of_div_le_neg Hb H')))

  theorem div_le_div_of_le_neg (Hb : b < 0) (H : a ≤ b) : 1 / b ≤ 1 / a :=
    le_of_not_lt
      (assume H',
      absurd H (not_le_of_lt (lt_of_div_lt_neg Hb H')))

  -- belongs in ordered ring?
  theorem zero_gt_neg_one : -1 < 0 :=
    neg_zero ▸ (neg_lt_neg zero_lt_one)

  theorem exists_lt : ∃ x, x < a := 
    have H : a - 1 < a, from add_lt_of_le_of_neg (le.refl _) zero_gt_neg_one,
    exists.intro _ H

  theorem exists_gt : ∃ x, x > a := 
    have H : a + 1 > a, from lt_add_of_le_of_pos (le.refl _) zero_lt_one,
    exists.intro _ H

  theorem one_lt_div (H1 : 0 < a) (H2 : a < 1) : 1 < 1 / a :=
    one_div_one ▸ div_lt_div_of_lt H1 H2

  theorem one_le_div (H1 : 0 < a) (H2 : a ≤ 1) : 1 ≤ 1 / a :=
    one_div_one ▸ div_le_div_of_le H1 H2

  theorem neg_one_lt_div_neg (H1 : a < 0) (H2 : -1 < a) : 1 / a < -1 :=
    one_div_neg_one_eq_neg_one ▸ div_lt_div_of_lt_neg H1 H2

  theorem neg_one_le_div_neg (H1 : a < 0) (H2 : -1 ≤ a) : 1 / a ≤ -1 :=
    one_div_neg_one_eq_neg_one ▸ div_le_div_of_le_neg H1 H2


  -- the following theorems amount to four iffs, for <, ≤, ≥, >. 

  theorem mul_le_of_le_div (Hc : 0 < c) (H : a ≤ b / c) : a * c ≤ b := 
    div_mul_cancel (ne.symm (ne_of_lt Hc)) ▸ mul_le_mul_of_nonneg_right H (le_of_lt Hc)
 
  theorem le_div_of_mul_le (Hc : 0 < c) (H : a * c ≤ b) : a ≤ b / c :=
    calc
      a   = a * c * (1 / c) : mul_mul_div (ne.symm (ne_of_lt Hc))
      ... ≤ b * (1 / c)     : mul_le_mul_of_nonneg_right H (le_of_lt (div_pos_of_pos Hc))
      ... = b / c           : div_eq_mul_one_div

  theorem mul_lt_of_lt_div (Hc : 0 < c) (H : a < b / c) : a * c < b :=
    div_mul_cancel (ne.symm (ne_of_lt Hc)) ▸ mul_lt_mul_of_pos_right H Hc

  theorem lt_div_of_mul_lt (Hc : 0 < c) (H : a * c < b) : a < b / c :=
    calc
      a   = a * c * (1 / c) : mul_mul_div (ne.symm (ne_of_lt Hc))
      ... < b * (1 / c)     : mul_lt_mul_of_pos_right H (div_pos_of_pos Hc)
      ... = b / c           : div_eq_mul_one_div

  theorem mul_le_of_ge_div_neg (Hc : c < 0) (H : a ≥ b / c) : a * c ≤ b :=
    div_mul_cancel (ne_of_lt Hc) ▸ mul_le_mul_of_nonpos_right H (le_of_lt Hc)

  theorem ge_div_of_mul_le_neg (Hc : c < 0) (H : a * c ≤ b) : a ≥ b / c := 
    calc
      a   = a * c * (1 / c) : mul_mul_div (ne_of_lt Hc)
      ... ≥ b * (1 / c)     : mul_le_mul_of_nonpos_right H (le_of_lt (div_neg_of_neg Hc))
      ... = b / c           : div_eq_mul_one_div
 
  theorem mul_lt_of_gt_div_neg (Hc : c < 0) (H : a > b / c) : a * c < b :=
    div_mul_cancel (ne_of_lt Hc) ▸ mul_lt_mul_of_neg_right H Hc

  theorem gt_div_of_mul_gt_neg (Hc : c < 0) (H : a * c < b) : a > b / c :=
    calc
      a   = a * c * (1 / c) : mul_mul_div (ne_of_lt Hc)
      ... > b * (1 / c)     : mul_lt_mul_of_neg_right H (div_neg_of_neg Hc)
      ... = b / c           : div_eq_mul_one_div

end linear_ordered_field

structure discrete_linear_ordered_field [class] (A : Type) extends linear_ordered_field A,
  decidable_linear_ordered_comm_ring A

section discrete_linear_ordered_field
  
  variable {A : Type}
  variables [s : discrete_linear_ordered_field A] {a b c : A}
  include s


  theorem dec_eq_of_dec_lt : ∀ x y : A, decidable (x = y) := 
    take x y,
    decidable.by_cases
    (assume H : x < y, decidable.inr (ne_of_lt H))
    (assume H : ¬ x < y,
      decidable.by_cases
      (assume H' : y < x, decidable.inr (ne.symm (ne_of_lt H')))
      (assume H' : ¬ y < x, 
        decidable.inl (le.antisymm (le_of_not_lt H') (le_of_not_lt H))))

  definition discrete_linear_ordered_field.to_discrete_field [instance] [reducible] [coercion]
    [s : discrete_linear_ordered_field A] :  discrete_field A :=
      ⦃ discrete_field, s, decidable_equality := dec_eq_of_dec_lt⦄



end discrete_linear_ordered_field
end algebra
