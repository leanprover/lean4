/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

Here an "ordered_ring" is partially ordered ring, which is ordered with respect to both a weak
order and an associated strict order. Our numeric structures (int, rat, and real) will be instances
of "linear_ordered_comm_ring". This development is modeled after Isabelle's library.
-/

import algebra.ordered_group algebra.ring
open eq eq.ops

namespace algebra

variable {A : Type}

definition absurd_a_lt_a {B : Type} {a : A} [s : strict_order A] (H : a < a) : B :=
absurd H (lt.irrefl a)

structure ordered_semiring [class] (A : Type)
  extends semiring A, ordered_cancel_comm_monoid A :=
(mul_le_mul_of_nonneg_left: ∀a b c, le a b → le zero c → le (mul c a) (mul c b))
(mul_le_mul_of_nonneg_right: ∀a b c, le a b → le zero c → le (mul a c) (mul b c))
(mul_lt_mul_of_pos_left: ∀a b c, lt a b → lt zero c → lt (mul c a) (mul c b))
(mul_lt_mul_of_pos_right: ∀a b c, lt a b → lt zero c → lt (mul a c) (mul b c))

section
  variable [s : ordered_semiring A]
  variables (a b c d e : A)
  include s

  theorem mul_le_mul_of_nonneg_left {a b c : A} (Hab : a ≤ b) (Hc : 0 ≤ c) :
    c * a ≤ c * b := !ordered_semiring.mul_le_mul_of_nonneg_left Hab Hc

  theorem mul_le_mul_of_nonneg_right {a b c : A} (Hab : a ≤ b) (Hc : 0 ≤ c) :
    a * c ≤ b * c := !ordered_semiring.mul_le_mul_of_nonneg_right Hab Hc

  -- TODO: there are four variations, depending on which variables we assume to be nonneg
  theorem mul_le_mul {a b c d : A} (Hac : a ≤ c) (Hbd : b ≤ d) (nn_b : 0 ≤ b) (nn_c : 0 ≤ c) :
    a * b ≤ c * d :=
  calc
    a * b ≤ c * b : mul_le_mul_of_nonneg_right Hac nn_b
      ... ≤ c * d : mul_le_mul_of_nonneg_left Hbd nn_c

  theorem mul_nonneg {a b : A} (Ha : a ≥ 0) (Hb : b ≥ 0) : a * b ≥ 0 :=
  begin
    have H : 0 * b ≤ a * b, from mul_le_mul_of_nonneg_right Ha Hb,
    rewrite zero_mul at H,
    exact H
  end

  theorem mul_nonpos_of_nonneg_of_nonpos {a b : A} (Ha : a ≥ 0) (Hb : b ≤ 0) : a * b ≤ 0 :=
  begin
    have H : a * b ≤ a * 0, from mul_le_mul_of_nonneg_left Hb Ha,
    rewrite mul_zero at H,
    exact H
  end

  theorem mul_nonpos_of_nonpos_of_nonneg {a b : A} (Ha : a ≤ 0) (Hb : b ≥ 0) : a * b ≤ 0 :=
  begin
    have H : a * b ≤ 0 * b, from mul_le_mul_of_nonneg_right Ha Hb,
    rewrite zero_mul at H,
    exact H
  end

  theorem mul_lt_mul_of_pos_left {a b c : A} (Hab : a < b) (Hc : 0 < c) :
    c * a < c * b := !ordered_semiring.mul_lt_mul_of_pos_left Hab Hc

  theorem mul_lt_mul_of_pos_right {a b c : A} (Hab : a < b) (Hc : 0 < c) :
    a * c < b * c := !ordered_semiring.mul_lt_mul_of_pos_right Hab Hc

  -- TODO: once again, there are variations
  theorem mul_lt_mul {a b c d : A} (Hac : a < c) (Hbd : b ≤ d) (pos_b : 0 < b) (nn_c : 0 ≤ c) :
    a * b < c * d :=
  calc
    a * b < c * b : mul_lt_mul_of_pos_right Hac pos_b
      ... ≤ c * d : mul_le_mul_of_nonneg_left Hbd nn_c

  theorem mul_pos {a b : A} (Ha : a > 0) (Hb : b > 0) : a * b > 0 :=
  begin
    have H : 0 * b < a * b, from mul_lt_mul_of_pos_right Ha Hb,
    rewrite zero_mul at H,
    exact H
  end

  theorem mul_neg_of_pos_of_neg {a b : A} (Ha : a > 0) (Hb : b < 0) : a * b < 0 :=
  begin
    have H : a * b < a * 0, from mul_lt_mul_of_pos_left Hb Ha,
    rewrite mul_zero at H,
    exact H
  end

  theorem mul_neg_of_neg_of_pos {a b : A} (Ha : a < 0) (Hb : b > 0) : a * b < 0 :=
  begin
    have H : a * b < 0 * b, from mul_lt_mul_of_pos_right Ha Hb,
    rewrite zero_mul at  H,
    exact H
  end
end

structure linear_ordered_semiring [class] (A : Type)
  extends ordered_semiring A, linear_strong_order_pair A :=
(zero_lt_one : lt zero one)

section
  variable [s : linear_ordered_semiring A]
  variables {a b c : A}
  include s

  theorem zero_lt_one : 0 < (1:A) := linear_ordered_semiring.zero_lt_one A

  theorem lt_of_mul_lt_mul_left (H : c * a < c * b) (Hc : c ≥ 0) : a < b :=
  lt_of_not_ge
    (assume H1 : b ≤ a,
      have H2 : c * b ≤ c * a, from mul_le_mul_of_nonneg_left H1 Hc,
      not_lt_of_ge H2 H)

  theorem lt_of_mul_lt_mul_right (H : a * c < b * c) (Hc : c ≥ 0) : a < b :=
  lt_of_not_ge
    (assume H1 : b ≤ a,
      have H2 : b * c ≤ a * c, from mul_le_mul_of_nonneg_right H1 Hc,
      not_lt_of_ge H2 H)

  theorem le_of_mul_le_mul_left (H : c * a ≤ c * b) (Hc : c > 0) : a ≤ b :=
  le_of_not_gt
    (assume H1 : b < a,
      have H2 : c * b < c * a, from mul_lt_mul_of_pos_left H1 Hc,
      not_le_of_gt H2 H)

  theorem le_of_mul_le_mul_right (H : a * c ≤ b * c) (Hc : c > 0) : a ≤ b :=
  le_of_not_gt
    (assume H1 : b < a,
      have H2 : b * c < a * c, from mul_lt_mul_of_pos_right H1 Hc,
      not_le_of_gt H2 H)

  theorem le_iff_mul_le_mul_left (a b : A) {c : A} (H : c > 0) : a ≤ b ↔ c * a ≤ c * b :=
  iff.intro
    (assume H', mul_le_mul_of_nonneg_left H' (le_of_lt H))
    (assume H', le_of_mul_le_mul_left H' H)

  theorem le_iff_mul_le_mul_right (a b : A) {c : A} (H : c > 0) : a ≤ b ↔ a * c ≤ b * c :=
  iff.intro
    (assume H', mul_le_mul_of_nonneg_right H' (le_of_lt H))
    (assume H', le_of_mul_le_mul_right H' H)

  theorem pos_of_mul_pos_left (H : 0 < a * b) (H1 : 0 ≤ a) : 0 < b :=
  lt_of_not_ge
    (assume H2 : b ≤ 0,
      have H3 : a * b ≤ 0, from mul_nonpos_of_nonneg_of_nonpos H1 H2,
      not_lt_of_ge H3 H)

  theorem pos_of_mul_pos_right (H : 0 < a * b) (H1 : 0 ≤ b) : 0 < a :=
  lt_of_not_ge
    (assume H2 : a ≤ 0,
      have H3 : a * b ≤ 0, from mul_nonpos_of_nonpos_of_nonneg H2 H1,
      not_lt_of_ge H3 H)

  theorem nonneg_of_mul_nonneg_left (H : 0 ≤ a * b) (H1 : 0 < a) : 0 ≤ b :=
  le_of_not_gt
    (assume H2 : b < 0,
      not_le_of_gt (mul_neg_of_pos_of_neg H1 H2) H)

  theorem nonneg_of_mul_nonneg_right (H : 0 ≤ a * b) (H1 : 0 < b) : 0 ≤ a :=
  le_of_not_gt
    (assume H2 : a < 0,
      not_le_of_gt (mul_neg_of_neg_of_pos H2 H1) H)

  theorem neg_of_mul_neg_left (H : a * b < 0) (H1 : 0 ≤ a) : b < 0 :=
  lt_of_not_ge
    (assume H2 : b ≥ 0,
      not_lt_of_ge (mul_nonneg H1 H2) H)

  theorem neg_of_mul_neg_right (H : a * b < 0) (H1 : 0 ≤ b) : a < 0 :=
  lt_of_not_ge
    (assume H2 : a ≥ 0,
      not_lt_of_ge (mul_nonneg H2 H1) H)

  theorem nonpos_of_mul_nonpos_left (H : a * b ≤ 0) (H1 : 0 < a) : b ≤ 0 :=
  le_of_not_gt
    (assume H2 : b > 0,
      not_le_of_gt (mul_pos H1 H2) H)

  theorem nonpos_of_mul_nonpos_right (H : a * b ≤ 0) (H1 : 0 < b) : a ≤ 0 :=
  le_of_not_gt
    (assume H2 : a > 0,
      not_le_of_gt (mul_pos H2 H1) H)
end

structure ordered_ring [class] (A : Type)
    extends ring A, ordered_comm_group A, zero_ne_one_class A :=
(mul_nonneg : ∀a b, le zero a → le zero b → le zero (mul a b))
(mul_pos : ∀a b, lt zero a → lt zero b → lt zero (mul a b))

theorem ordered_ring.mul_le_mul_of_nonneg_left [s : ordered_ring A] {a b c : A}
        (Hab : a ≤ b) (Hc : 0 ≤ c) : c * a ≤ c * b :=
have H1 : 0 ≤ b - a, from iff.elim_right !sub_nonneg_iff_le Hab,
assert H2 : 0 ≤ c * (b - a), from ordered_ring.mul_nonneg _ _ Hc H1,
begin
  rewrite mul_sub_left_distrib at H2,
  exact (iff.mp !sub_nonneg_iff_le H2)
end

theorem ordered_ring.mul_le_mul_of_nonneg_right [s : ordered_ring A] {a b c : A}
        (Hab : a ≤ b) (Hc : 0 ≤ c) : a * c ≤ b * c  :=
have H1 : 0 ≤ b - a, from iff.elim_right !sub_nonneg_iff_le Hab,
assert H2 : 0 ≤ (b - a) * c, from ordered_ring.mul_nonneg _ _ H1 Hc,
begin
  rewrite mul_sub_right_distrib at H2,
  exact (iff.mp !sub_nonneg_iff_le H2)
end

theorem ordered_ring.mul_lt_mul_of_pos_left [s : ordered_ring A] {a b c : A}
       (Hab : a < b) (Hc : 0 < c) : c * a < c * b :=
have H1 : 0 < b - a, from iff.elim_right !sub_pos_iff_lt Hab,
assert H2 : 0 < c * (b - a), from ordered_ring.mul_pos _ _ Hc H1,
begin
  rewrite mul_sub_left_distrib at H2,
  exact (iff.mp !sub_pos_iff_lt H2)
end

theorem ordered_ring.mul_lt_mul_of_pos_right [s : ordered_ring A] {a b c : A}
       (Hab : a < b) (Hc : 0 < c) : a * c < b * c :=
have H1 : 0 < b - a, from iff.elim_right !sub_pos_iff_lt Hab,
assert H2 : 0 < (b - a) * c, from ordered_ring.mul_pos _ _ H1 Hc,
begin
  rewrite mul_sub_right_distrib at H2,
  exact (iff.mp !sub_pos_iff_lt H2)
end

definition ordered_ring.to_ordered_semiring [trans-instance] [coercion] [reducible]
    [s : ordered_ring A] :
  ordered_semiring A :=
⦃ ordered_semiring, s,
  mul_zero                   := mul_zero,
  zero_mul                   := zero_mul,
  add_left_cancel            := @add.left_cancel A s,
  add_right_cancel           := @add.right_cancel A s,
  le_of_add_le_add_left      := @le_of_add_le_add_left A s,
  mul_le_mul_of_nonneg_left  := @ordered_ring.mul_le_mul_of_nonneg_left A s,
  mul_le_mul_of_nonneg_right := @ordered_ring.mul_le_mul_of_nonneg_right A s,
  mul_lt_mul_of_pos_left     := @ordered_ring.mul_lt_mul_of_pos_left A s,
  mul_lt_mul_of_pos_right    := @ordered_ring.mul_lt_mul_of_pos_right A s,
  lt_of_add_lt_add_left      := @lt_of_add_lt_add_left A s⦄

section
  variable [s : ordered_ring A]
  variables {a b c : A}
  include s

  theorem mul_le_mul_of_nonpos_left (H : b ≤ a) (Hc : c ≤ 0) : c * a ≤ c * b :=
  have Hc' : -c ≥ 0, from iff.mpr !neg_nonneg_iff_nonpos Hc,
  assert H1 : -c * b ≤ -c * a, from mul_le_mul_of_nonneg_left H Hc',
  have H2 : -(c * b) ≤ -(c * a),
    begin
      rewrite [-*neg_mul_eq_neg_mul at H1],
      exact H1
    end,
  iff.mp !neg_le_neg_iff_le H2

  theorem mul_le_mul_of_nonpos_right (H : b ≤ a) (Hc : c ≤ 0) : a * c ≤ b * c :=
  have Hc' : -c ≥ 0, from iff.mpr !neg_nonneg_iff_nonpos Hc,
  assert H1 : b * -c ≤ a * -c, from mul_le_mul_of_nonneg_right H Hc',
  have H2 : -(b * c) ≤ -(a * c),
    begin
      rewrite [-*neg_mul_eq_mul_neg at H1],
      exact H1
    end,
  iff.mp !neg_le_neg_iff_le H2

  theorem mul_nonneg_of_nonpos_of_nonpos (Ha : a ≤ 0) (Hb : b ≤ 0) : 0 ≤ a * b :=
  begin
    have H : 0 * b ≤ a * b, from mul_le_mul_of_nonpos_right Ha Hb,
    rewrite zero_mul at H,
    exact H
  end

  theorem mul_lt_mul_of_neg_left (H : b < a) (Hc : c < 0) : c * a < c * b :=
  have Hc' : -c > 0, from iff.mpr !neg_pos_iff_neg Hc,
  assert H1 : -c * b < -c * a, from mul_lt_mul_of_pos_left H Hc',
  have H2 : -(c * b) < -(c * a),
    begin
      rewrite [-*neg_mul_eq_neg_mul at H1],
      exact H1
    end,
  iff.mp !neg_lt_neg_iff_lt H2

  theorem mul_lt_mul_of_neg_right (H : b < a) (Hc : c < 0) : a * c < b * c :=
  have Hc' : -c > 0, from iff.mpr !neg_pos_iff_neg Hc,
  assert H1 : b * -c < a * -c, from mul_lt_mul_of_pos_right H Hc',
  have H2 : -(b * c) < -(a * c),
    begin
      rewrite [-*neg_mul_eq_mul_neg at H1],
      exact H1
    end,
  iff.mp !neg_lt_neg_iff_lt H2

  theorem mul_pos_of_neg_of_neg (Ha : a < 0) (Hb : b < 0) : 0 < a * b :=
  begin
    have H : 0 * b < a * b, from mul_lt_mul_of_neg_right Ha Hb,
    rewrite zero_mul at H,
    exact H
  end

end

-- TODO: we can eliminate mul_pos_of_pos, but now it is not worth the effort to redeclare the
-- class instance
structure linear_ordered_ring [class] (A : Type)
    extends ordered_ring A, linear_strong_order_pair A :=
  (zero_lt_one : lt zero one)

definition linear_ordered_ring.to_linear_ordered_semiring [trans-instance] [coercion] [reducible]
    [s : linear_ordered_ring A] :
  linear_ordered_semiring A :=
⦃ linear_ordered_semiring, s,
  mul_zero                   := mul_zero,
  zero_mul                   := zero_mul,
  add_left_cancel            := @add.left_cancel A s,
  add_right_cancel           := @add.right_cancel A s,
  le_of_add_le_add_left      := @le_of_add_le_add_left A s,
  mul_le_mul_of_nonneg_left  := @mul_le_mul_of_nonneg_left A s,
  mul_le_mul_of_nonneg_right := @mul_le_mul_of_nonneg_right A s,
  mul_lt_mul_of_pos_left     := @mul_lt_mul_of_pos_left A s,
  mul_lt_mul_of_pos_right    := @mul_lt_mul_of_pos_right A s,
  le_total                   := linear_ordered_ring.le_total,
  lt_of_add_lt_add_left      := @lt_of_add_lt_add_left A s ⦄

structure linear_ordered_comm_ring [class] (A : Type) extends linear_ordered_ring A, comm_monoid A

theorem linear_ordered_comm_ring.eq_zero_or_eq_zero_of_mul_eq_zero [s : linear_ordered_comm_ring A]
        {a b : A} (H : a * b = 0) : a = 0 ∨ b = 0 :=
lt.by_cases
  (assume Ha : 0 < a,
    lt.by_cases
      (assume Hb : 0 < b,
        begin
          have H1 : 0 < a * b, from mul_pos Ha Hb,
          rewrite H at H1,
          apply absurd_a_lt_a H1
        end)
      (assume Hb : 0 = b, or.inr (Hb⁻¹))
      (assume Hb : 0 > b,
        begin
          have H1 : 0 > a * b, from mul_neg_of_pos_of_neg Ha Hb,
          rewrite H at H1,
          apply absurd_a_lt_a H1
        end))
  (assume Ha : 0 = a, or.inl (Ha⁻¹))
  (assume Ha : 0 > a,
    lt.by_cases
      (assume Hb : 0 < b,
        begin
          have H1 : 0 > a * b, from mul_neg_of_neg_of_pos Ha Hb,
          rewrite H at H1,
          apply absurd_a_lt_a H1
        end)
      (assume Hb : 0 = b, or.inr (Hb⁻¹))
      (assume Hb : 0 > b,
        begin
          have H1 : 0 < a * b, from mul_pos_of_neg_of_neg Ha Hb,
          rewrite H at H1,
          apply absurd_a_lt_a H1
        end))

-- Linearity implies no zero divisors. Doesn't need commutativity.
definition linear_ordered_comm_ring.to_integral_domain [trans-instance] [coercion] [reducible]
    [s: linear_ordered_comm_ring A] : integral_domain A :=
⦃ integral_domain, s,
  eq_zero_or_eq_zero_of_mul_eq_zero :=
     @linear_ordered_comm_ring.eq_zero_or_eq_zero_of_mul_eq_zero A s ⦄

section
  variable [s : linear_ordered_ring A]
  variables (a b c : A)
  include s

  theorem mul_self_nonneg : a * a ≥ 0 :=
  or.elim (le.total 0 a)
    (assume H : a ≥ 0, mul_nonneg H H)
    (assume H : a ≤ 0, mul_nonneg_of_nonpos_of_nonpos H H)

  theorem zero_le_one : 0 ≤ (1:A) := one_mul 1 ▸ mul_self_nonneg 1

  theorem pos_and_pos_or_neg_and_neg_of_mul_pos {a b : A} (Hab : a * b > 0) :
    (a > 0 ∧ b > 0) ∨ (a < 0 ∧ b < 0) :=
  lt.by_cases
    (assume Ha : 0 < a,
      lt.by_cases
        (assume Hb : 0 < b, or.inl (and.intro Ha Hb))
        (assume Hb : 0 = b,
          begin
            rewrite [-Hb at Hab, mul_zero at Hab],
            apply absurd_a_lt_a Hab
          end)
        (assume Hb : b < 0,
          absurd Hab (lt.asymm (mul_neg_of_pos_of_neg Ha Hb))))
    (assume Ha : 0 = a,
      begin
        rewrite [-Ha at Hab, zero_mul at Hab],
        apply absurd_a_lt_a Hab
      end)
    (assume Ha : a < 0,
      lt.by_cases
        (assume Hb : 0 < b,
          absurd Hab (lt.asymm (mul_neg_of_neg_of_pos Ha Hb)))
        (assume Hb : 0 = b,
          begin
            rewrite [-Hb at Hab, mul_zero at Hab],
            apply absurd_a_lt_a Hab
          end)
        (assume Hb : b < 0, or.inr (and.intro Ha Hb)))

  theorem gt_of_mul_lt_mul_neg_left {a b c : A} (H : c * a < c * b) (Hc : c ≤ 0) : a > b :=
    have nhc : -c ≥ 0, from neg_nonneg_of_nonpos Hc,
    have H2 : -(c * b) < -(c * a), from iff.mpr (neg_lt_neg_iff_lt _ _) H,
    have H3 : (-c) * b < (-c) * a, from calc
      (-c) * b = - (c * b)    : neg_mul_eq_neg_mul
           ... < -(c * a)     : H2
           ... = (-c) * a     : neg_mul_eq_neg_mul,
    lt_of_mul_lt_mul_left H3 nhc

  theorem zero_gt_neg_one : -1 < (0:A) :=
    neg_zero ▸ (neg_lt_neg zero_lt_one)

  theorem le_of_mul_le_of_ge_one {a b c : A} (H : a * c ≤ b) (Hb : b ≥ 0) (Hc : c ≥ 1) : a ≤ b :=
    have H' : a * c ≤ b * c, from calc
      a * c ≤ b : H
        ... = b * 1 : mul_one
        ... ≤ b * c : mul_le_mul_of_nonneg_left Hc Hb,
    le_of_mul_le_mul_right H' (lt_of_lt_of_le zero_lt_one Hc)

end

/- TODO: Isabelle's library has all kinds of cancelation rules for the simplifier.
   Search on mult_le_cancel_right1 in Rings.thy. -/

structure decidable_linear_ordered_comm_ring [class] (A : Type) extends linear_ordered_comm_ring A,
    decidable_linear_ordered_comm_group A

section
  variable [s : decidable_linear_ordered_comm_ring A]
  variables {a b c : A}
  include s

  definition sign (a : A) : A := lt.cases a 0 (-1) 0 1

  theorem sign_of_neg (H : a < 0) : sign a = -1 := lt.cases_of_lt H

  theorem sign_zero : sign 0 = (0:A) := lt.cases_of_eq rfl

  theorem sign_of_pos (H : a > 0) : sign a = 1 := lt.cases_of_gt H

  theorem sign_one : sign 1 = (1:A) := sign_of_pos zero_lt_one

  theorem sign_neg_one : sign (-1) = -(1:A) := sign_of_neg (neg_neg_of_pos zero_lt_one)

  theorem sign_sign (a : A) : sign (sign a) = sign a :=
  lt.by_cases
    (assume H : a > 0,
      calc
        sign (sign a) = sign 1 : by rewrite (sign_of_pos H)
                  ... = 1      : by rewrite sign_one
                  ... = sign a : by rewrite (sign_of_pos H))
    (assume H : 0 = a,
      calc
        sign (sign a) = sign (sign 0) : by rewrite H
                  ... = sign 0        : by rewrite sign_zero at {1}
                  ... = sign a        : by rewrite -H)
    (assume H : a < 0,
      calc
        sign (sign a) = sign (-1)     : by rewrite (sign_of_neg H)
                  ... = -1            : by rewrite sign_neg_one
                  ... = sign a        : by rewrite (sign_of_neg H))

  theorem pos_of_sign_eq_one (H : sign a = 1) : a > 0 :=
  lt.by_cases
    (assume H1 : 0 < a, H1)
    (assume H1 : 0 = a,
      begin
        rewrite [-H1 at H, sign_zero at H],
        apply absurd H zero_ne_one
      end)
    (assume H1 : 0 > a,
      have H2 : -1 = 1, from (sign_of_neg H1)⁻¹ ⬝ H,
      absurd ((eq_zero_of_neg_eq H2)⁻¹) zero_ne_one)

  theorem eq_zero_of_sign_eq_zero (H : sign a = 0) : a = 0 :=
  lt.by_cases
    (assume H1 : 0 < a,
      absurd (H⁻¹ ⬝ sign_of_pos H1) zero_ne_one)
    (assume H1 : 0 = a, H1⁻¹)
    (assume H1 : 0 > a,
      have H2 : 0 = -1, from H⁻¹ ⬝ sign_of_neg H1,
      have H3 : 1 = 0, from eq_neg_of_eq_neg H2 ⬝ neg_zero,
      absurd (H3⁻¹) zero_ne_one)

  theorem neg_of_sign_eq_neg_one (H : sign a = -1) : a < 0 :=
  lt.by_cases
    (assume H1 : 0 < a,
      have H2 : -1 = 1, from H⁻¹ ⬝ (sign_of_pos H1),
      absurd ((eq_zero_of_neg_eq H2)⁻¹) zero_ne_one)
    (assume H1 : 0 = a,
      have H2 : (0:A) = -1,
        begin
          rewrite [-H1 at H, sign_zero at H],
          exact H
        end,
      have H3 : 1 = 0, from eq_neg_of_eq_neg H2 ⬝ neg_zero,
      absurd (H3⁻¹) zero_ne_one)
    (assume H1 : 0 > a, H1)

  theorem sign_neg (a : A) : sign (-a) = -(sign a) :=
  lt.by_cases
    (assume H1 : 0 < a,
      calc
        sign (-a) = -1        : sign_of_neg (neg_neg_of_pos H1)
              ... = -(sign a) : by rewrite (sign_of_pos H1))
    (assume H1 : 0 = a,
      calc
        sign (-a) = sign (-0) : by rewrite H1
              ... = sign 0    : by rewrite neg_zero
              ... = 0         : by rewrite sign_zero
              ... = -0        : by rewrite neg_zero
              ... = -(sign 0) : by rewrite sign_zero
              ... = -(sign a) : by rewrite -H1)
    (assume H1 : 0 > a,
      calc
        sign (-a) = 1         : sign_of_pos (neg_pos_of_neg H1)
              ... = -(-1)     : by rewrite neg_neg
              ... = -(sign a) : sign_of_neg H1)

  theorem sign_mul (a b : A) : sign (a * b) = sign a * sign b :=
  lt.by_cases
    (assume z_lt_a : 0 < a,
      lt.by_cases
       (assume z_lt_b : 0 < b,
         by rewrite [sign_of_pos z_lt_a, sign_of_pos z_lt_b,
                     sign_of_pos (mul_pos z_lt_a z_lt_b), one_mul])
       (assume z_eq_b : 0 = b, by rewrite [-z_eq_b, mul_zero, *sign_zero, mul_zero])
       (assume z_gt_b : 0 > b,
         by rewrite [sign_of_pos z_lt_a, sign_of_neg z_gt_b,
                     sign_of_neg (mul_neg_of_pos_of_neg z_lt_a z_gt_b), one_mul]))
    (assume z_eq_a : 0 = a, by rewrite [-z_eq_a, zero_mul, *sign_zero, zero_mul])
    (assume z_gt_a : 0 > a,
      lt.by_cases
       (assume z_lt_b : 0 < b,
         by rewrite [sign_of_neg z_gt_a, sign_of_pos z_lt_b,
                     sign_of_neg (mul_neg_of_neg_of_pos z_gt_a z_lt_b), mul_one])
       (assume z_eq_b : 0 = b, by rewrite [-z_eq_b, mul_zero, *sign_zero, mul_zero])
       (assume z_gt_b : 0 > b,
         by rewrite [sign_of_neg z_gt_a, sign_of_neg z_gt_b,
                     sign_of_pos (mul_pos_of_neg_of_neg z_gt_a z_gt_b),
                     neg_mul_neg, one_mul]))

  theorem abs_eq_sign_mul (a : A) : abs a = sign a * a :=
  lt.by_cases
    (assume H1 : 0 < a,
      calc
        abs a = a          : abs_of_pos H1
        ... = 1 * a        : by rewrite one_mul
        ... = sign a * a   : by rewrite (sign_of_pos H1))
    (assume H1 : 0 = a,
      calc
        abs a = abs 0    : by rewrite H1
        ... = 0          : by rewrite abs_zero
        ... = 0 * a      : by rewrite zero_mul
        ... = sign 0 * a : by rewrite sign_zero
        ... = sign a * a : by rewrite H1)
    (assume H1 : a < 0,
      calc
        abs a = -a         : abs_of_neg H1
          ... = -1 * a     : by rewrite neg_eq_neg_one_mul
          ... = sign a * a : by rewrite (sign_of_neg H1))

  theorem eq_sign_mul_abs (a : A) : a = sign a * abs a :=
  lt.by_cases
    (assume H1 : 0 < a,
      calc
        a = abs a              : abs_of_pos H1
          ... = 1 * abs a      : by rewrite one_mul
          ... = sign a * abs a : by rewrite (sign_of_pos H1))
    (assume H1 : 0 = a,
      calc
        a = 0                  : H1⁻¹
          ... = 0 * abs a      : by rewrite zero_mul
          ... = sign 0 * abs a : by rewrite sign_zero
          ... = sign a * abs a : by rewrite H1)
    (assume H1 : a < 0,
      calc
        a = -(-a)              : by rewrite neg_neg
          ... = -abs a         : by rewrite (abs_of_neg H1)
          ... = -1 * abs a     : by rewrite neg_eq_neg_one_mul
          ... = sign a * abs a : by rewrite (sign_of_neg H1))

  theorem abs_dvd_iff (a b : A) : abs a ∣ b ↔ a ∣ b :=
  abs.by_cases !iff.refl !neg_dvd_iff_dvd

  theorem dvd_abs_iff (a b : A) : a ∣ abs b ↔ a ∣ b :=
  abs.by_cases !iff.refl !dvd_neg_iff_dvd

  theorem abs_mul (a b : A) : abs (a * b) = abs a * abs b :=
  or.elim (le.total 0 a)
    (assume H1 : 0 ≤ a,
      or.elim (le.total 0 b)
        (assume H2 : 0 ≤ b,
          calc
            abs (a * b) = a * b         : abs_of_nonneg (mul_nonneg H1 H2)
                    ... = abs a * b     : by rewrite (abs_of_nonneg H1)
                    ... = abs a * abs b : by rewrite (abs_of_nonneg H2))
        (assume H2 : b ≤ 0,
          calc
            abs (a * b) = -(a * b)      : abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos H1 H2)
                    ... = a * -b        : by rewrite neg_mul_eq_mul_neg
                    ... = abs a * -b    : by rewrite (abs_of_nonneg H1)
                    ... = abs a * abs b : by rewrite (abs_of_nonpos H2)))
    (assume H1 : a ≤ 0,
      or.elim (le.total 0 b)
        (assume H2 : 0 ≤ b,
          calc
            abs (a * b) = -(a * b)      : abs_of_nonpos (mul_nonpos_of_nonpos_of_nonneg H1 H2)
                    ... = -a * b        : by rewrite neg_mul_eq_neg_mul
                    ... = abs a * b     : by rewrite (abs_of_nonpos H1)
                    ... = abs a * abs b : by rewrite (abs_of_nonneg H2))
        (assume H2 : b ≤ 0,
          calc
            abs (a * b) = a * b         : abs_of_nonneg (mul_nonneg_of_nonpos_of_nonpos H1 H2)
                    ... = -a * -b       : by rewrite neg_mul_neg
                    ... = abs a * -b    : by rewrite (abs_of_nonpos H1)
                    ... = abs a * abs b : by rewrite (abs_of_nonpos H2)))

  theorem abs_mul_self (a : A) : abs a * abs a = a * a :=
  abs.by_cases rfl !neg_mul_neg
end

/- TODO: Multiplication and one, starting with mult_right_le_one_le. -/

end algebra
