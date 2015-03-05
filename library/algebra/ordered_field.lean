/-
Copyright (c) 2014 Robert Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: algebra.ordered_field
Authors: Robert Lewis

Here an "ordered_ring" is partially ordered ring, which is ordered with respect to both a weak
order and an associated strict order. Our numeric structures (int, rat, and real) will be instances
of "linear_ordered_comm_ring". This development is modeled after Isabelle's library.
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
  have H2 : -(c * b) < -(c * a), from (iff.mp' (neg_lt_neg_iff_lt _ _) H),
  have H3 : (-c) * b < (-c) * a, from (calc
    (-c) * b = (-1 * c) * b : neg_eq_neg_one_mul
    ... = -1 * (c * b) : mul.assoc
    ... = - (c * b) : neg_eq_neg_one_mul
    ... < -(c * a) : H2
    ... = -1 * (c * a) : neg_eq_neg_one_mul
    ... = (-1 * c) * a : mul.assoc
    ... = (-c) * a : neg_eq_neg_one_mul
  ),
  lt_of_mul_lt_mul_left H3 nhc

  -- helpers for following
  theorem mul_zero_lt_mul_inv_of_pos (H : 0 < a) : a * 0 < a * (1 / a) :=
   calc
      a * 0 = 0 : mul_zero
        ... < 1 : zero_lt_one
        ... = a * a⁻¹ : mul_inv_cancel (ne.symm (ne_of_lt H))
        ... = a * (1 / a) : inv_eq_one_div
 
  theorem mul_zero_lt_mul_inv_of_neg (H : a < 0) : a * 0 < a * (1 / a) :=
    calc
      a * 0 = 0 : mul_zero
        ... < 1 : zero_lt_one
        ... = a * a⁻¹ : mul_inv_cancel (ne_of_lt H)
        ... = a * (1 / a) : inv_eq_one_div
  
  theorem div_pos_of_pos (H : 0 < a) : 0 < 1 / a :=
    lt_of_mul_lt_mul_left (mul_zero_lt_mul_inv_of_pos H) (le_of_lt H)

  -- this would go in ring, if it worked
  theorem ne_zero_of_div_ne_zero (H : 1 / a ≠ 0) : a ≠ 0 :=
    assume Ha : a = 0, sorry

  theorem pos_of_div_pos (H : 0 < 1 / a) : 0 < a :=
    have H1 : 0 < 1 / (1 / a), from div_pos_of_pos H,
    -- want a ≠ 0. Can get this with decidable =, from discrete_field.inv_zero_imp_zero
    div_div (sorry) ▸ H1

  theorem div_neg_of_neg (H : a < 0) : 1 / a < 0 :=
    gt_of_mul_lt_mul_neg_left (mul_zero_lt_mul_inv_of_neg H) (le_of_lt H)

  theorem neg_of_div_neg (H : 1 / a < 0) : a < 0 :=
    sorry

  -- is this theorem (and le_of_div_le which depends on it) classical?
  theorem one_le_div_iff_le : 1 ≤ a / b ↔ b ≤ a := 
    sorry

  theorem one_lt_div_iff_lt : 1 < a / b ↔ b < a :=
    sorry

-- why is mul_le_mul under ordered_ring namespace?
  theorem le_of_div_le (H : 0 < a) (Hl : 1 / a ≤ 1 / b) : b ≤ a :=
    have H : 1 ≤ a / b, from (calc
      1 = a / a : div_self (ne.symm (ne_of_lt H))
      ... = a * (1 / a) :  div_eq_mul_one_div
      ... ≤ a * (1 / b) : ordered_ring.mul_le_mul_of_nonneg_left Hl (le_of_lt H)
      ... = a / b : div_eq_mul_one_div
      ), (iff.mp one_le_div_iff_le) H
      

  theorem lt_of_div_lt (H : a > 0) (Hl : 1 / a < 1 / b) : b < a :=
    have H : 1 < a / b, from (calc
      1 = a / a : div_self (ne.symm (ne_of_lt H))
      ... = a * (1 / a) :  div_eq_mul_one_div
      ... < a * (1 / b) : mul_lt_mul_of_pos_left Hl H
      ... = a / b : div_eq_mul_one_div
      ), (iff.mp one_lt_div_iff_lt) H

  theorem le_of_div_le_neg (H : b < 0) (Hl : 1 / a ≤ 1 / b) : b ≤ a :=
    have Ha : 1 / a < 0, from (calc
      1 / a ≤ 1 / b : Hl
      ... < 0 : div_neg_of_neg H
      ),
    have Ha' : a ≠ 0, from ne_of_lt (neg_of_div_neg Ha),
    have H : 1 ≤ a / b, from (calc
      1 = a / a : div_self Ha'
      ... ≤ a / b : sorry), sorry

  theorem lt_of_div_lt_pos (H : b < 0) (Hl : 1 / a < 1 / b) : b < a :=
    sorry

  theorem pos_iff_div_pos : a > 0 ↔ 1 / a > 0 :=
    sorry

end linear_ordered_field
end algebra
