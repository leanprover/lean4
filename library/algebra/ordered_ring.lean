/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: algebra.ordered_ring
Authors: Jeremy Avigad

Rather than multiply classes unnecessarily, we are aiming for the ones that are likely to be useful.
We can always split them apart later if necessary. Here an "ordered_ring" is partial ordered ring (which
is ordered with respect to both a weak order and an associated strict order). Our numeric structures will be
instances of "linear_ordered_comm_ring".

This development is modeled after Isabelle's library.
-/

import logic.eq data.unit data.sigma data.prod
import algebra.function algebra.binary algebra.ordered_group algebra.ring

open eq eq.ops

namespace algebra

variable {A : Type}

structure ordered_semiring [class] (A : Type) extends semiring A, ordered_cancel_comm_monoid A :=
(mul_le_mul_left: ∀a b c, le a b → le zero c → le (mul c a) (mul c b))
(mul_le_mul_right: ∀a b c, le a b → le zero c → le (mul a c) (mul b c))
(mul_lt_mul_left: ∀a b c, lt a b → lt zero c → lt (mul c a) (mul c b))
(mul_lt_mul_right: ∀a b c, lt a b → lt zero c → lt (mul a c) (mul b c))

section

  variable [s : ordered_semiring A]
  variables (a b c d e : A)
  include s

  -- TODO: remove after we short-circuit class-graph
  definition ordered_semiring.to_mul [instance] [priority 100000] : has_mul A :=
  has_mul.mk (@ordered_semiring.mul A s)
  definition ordered_semiring.to_lt [instance] [priority 100000] : has_lt A :=
  has_lt.mk (@ordered_semiring.lt A s)
  definition ordered_semiring.to_zero [instance] [priority 100000] : has_zero A :=
  has_zero.mk (@ordered_semiring.zero A s)

  theorem mul_le_mul_of_nonneg_left {a b c : A} (Hab : a ≤ b) (Hc : 0 ≤ c) :
    c * a ≤ c * b := !ordered_semiring.mul_le_mul_left Hab Hc

  theorem mul_le_mul_of_nonneg_right {a b c : A} (Hab : a ≤ b) (Hc : 0 ≤ c) :
    a * c ≤ b * c := !ordered_semiring.mul_le_mul_right Hab Hc

  -- TODO: there are four variations, depending on which variables we assume to be nonneg
  theorem mul_le_mul {a b c d : A} (Hac : a ≤ c) (Hbd : b ≤ d) (nn_b : 0 ≤ b) (nn_c : 0 ≤ c) :
    a * b ≤ c * d :=
  calc
    a * b ≤ c * b : mul_le_mul_of_nonneg_right Hac nn_b
      ... ≤ c * d : mul_le_mul_of_nonneg_left Hbd nn_c

  theorem mul_nonneg_of_nonneg_of_nonneg {a b : A} (Ha : a ≥ 0) (Hb : b ≥ 0) : a * b ≥ 0 :=
  have H : 0 * b ≤ a * b, from mul_le_mul_of_nonneg_right Ha Hb,
  !zero_mul ▸ H

  theorem mul_nonpos_of_nonneg_of_nonpos {a b : A} (Ha : a ≥ 0) (Hb : b ≤ 0) : a * b ≤ 0 :=
  have H : a * b ≤ a * 0, from mul_le_mul_of_nonneg_left Hb Ha,
  !mul_zero ▸ H

  theorem mul_nonpos_of_nonpos_of_nonneg {a b : A} (Ha : a ≤ 0) (Hb : b ≥ 0) : a * b ≤ 0 :=
  have H : a * b ≤ 0 * b, from mul_le_mul_of_nonneg_right Ha Hb,
  !zero_mul ▸ H

  theorem mul_lt_mul_of_pos_left {a b c : A} (Hab : a < b) (Hc : 0 < c) :
    c * a < c * b := !ordered_semiring.mul_lt_mul_left Hab Hc

  theorem mul_lt_mul_of_pos_right {a b c : A} (Hab : a < b) (Hc : 0 < c) :
    a * c < b * c := !ordered_semiring.mul_lt_mul_right Hab Hc

  -- TODO: once again, there are variations
  theorem mul_lt_mul {a b c d : A} (Hac : a < c) (Hbd : b ≤ d) (pos_b : 0 < b) (nn_c : 0 ≤ c) :
    a * b < c * d :=
  calc
    a * b < c * b : mul_lt_mul_of_pos_right Hac pos_b
      ... ≤ c * d : mul_le_mul_of_nonneg_left Hbd nn_c

  theorem mul_pos_of_pos_of_pos {a b : A} (Ha : a > 0) (Hb : b > 0) : a * b > 0 :=
  have H : 0 * b < a * b, from mul_lt_mul_of_pos_right Ha Hb,
  !zero_mul ▸ H

  theorem mul_neg_of_pos_of_neg {a b : A} (Ha : a > 0) (Hb : b < 0) : a * b < 0 :=
  have H : a * b < a * 0, from mul_lt_mul_of_pos_left Hb Ha,
  !mul_zero ▸ H

  theorem mul_neg_of_neg_of_pos {a b : A} (Ha : a < 0) (Hb : b > 0) : a * b < 0 :=
  have H : a * b < 0 * b, from mul_lt_mul_of_pos_right Ha Hb,
  !zero_mul ▸ H

end

structure linear_ordered_semiring [class] (A : Type)
    extends ordered_semiring A, linear_strong_order_pair A

section

  variable [s : linear_ordered_semiring A]
  variables (a b c : A)
  include s

  -- TODO: remove after we short-circuit class-graph
  definition linear_ordered_semiring.to_mul [instance] [priority 100000] : has_mul A :=
  has_mul.mk (@linear_ordered_semiring.mul A s)
  definition linear_ordered_semiring.to_lt [instance] [priority 100000] : has_lt A :=
  has_lt.mk (@linear_ordered_semiring.lt A s)
  definition linear_ordered_semiring.to_zero [instance] [priority 100000] : has_zero A :=
  has_zero.mk (@linear_ordered_semiring.zero A s)

  theorem lt_of_mul_lt_mul_left {a b c : A} (H : c * a < c * b) (Hc : c ≥ 0) : a < b :=
  lt_of_not_le
    (assume H1 : b ≤ a,
      have H2 : c * b ≤ c * a, from mul_le_mul_of_nonneg_left H1 Hc,
      not_lt_of_le H2 H)

  theorem lt_of_mul_lt_mul_right {a b c : A} (H : a * c < b * c) (Hc : c ≥ 0) : a < b :=
  lt_of_not_le
    (assume H1 : b ≤ a,
      have H2 : b * c ≤ a * c, from mul_le_mul_of_nonneg_right H1 Hc,
      not_lt_of_le H2 H)

  theorem le_of_mul_le_mul_left {a b c : A} (H : c * a ≤ c * b) (Hc : c > 0) : a ≤ b :=
  le_of_not_lt
    (assume H1 : b < a,
      have H2 : c * b < c * a, from mul_lt_mul_of_pos_left H1 Hc,
      not_le_of_lt H2 H)

  theorem le_of_mul_le_mul_right {a b c : A} (H : a * c ≤ b * c) (Hc : c > 0) : a ≤ b :=
  le_of_not_lt
    (assume H1 : b < a,
      have H2 : b * c < a * c, from mul_lt_mul_of_pos_right H1 Hc,
      not_le_of_lt H2 H)

  theorem pos_of_mul_pos_left (H : 0 < a * b) (H1 : 0 ≤ a) : 0 < b :=
  lt_of_not_le
    (assume H2 : b ≤ 0,
      have H3 : a * b ≤ 0, from mul_nonpos_of_nonneg_of_nonpos H1 H2,
      not_lt_of_le H3 H)

  theorem pos_of_mul_pos_right (H : 0 < a * b) (H1 : 0 ≤ b) : 0 < a :=
  lt_of_not_le
    (assume H2 : a ≤ 0,
      have H3 : a * b ≤ 0, from mul_nonpos_of_nonpos_of_nonneg H2 H1,
      not_lt_of_le H3 H)

end

structure ordered_ring [class] (A : Type) extends ring A, ordered_comm_group A :=
(mul_nonneg_of_nonneg_of_nonneg : ∀a b, le zero a → le zero b → le zero (mul a b))
(mul_pos_of_pos_of_pos : ∀a b, lt zero a → lt zero b → lt zero (mul a b))

definition ordered_ring.to_ordered_semiring [instance] [s : ordered_ring A] : ordered_semiring A :=
ordered_semiring.mk ordered_ring.add ordered_ring.add_assoc !ordered_ring.zero
  ordered_ring.zero_add ordered_ring.add_zero ordered_ring.add_comm ordered_ring.mul
  ordered_ring.mul_assoc !ordered_ring.one ordered_ring.one_mul ordered_ring.mul_one
  ordered_ring.left_distrib ordered_ring.right_distrib
  zero_mul mul_zero !ordered_ring.zero_ne_one
  (@add.left_cancel A _) (@add.right_cancel A _)
  ordered_ring.le ordered_ring.le_refl ordered_ring.le_trans ordered_ring.le_antisym
  ordered_ring.lt ordered_ring.lt_iff_le_ne ordered_ring.add_le_add_left
  (@le_of_add_le_add_left A _)
  (take a b c,
    assume Hab : a ≤ b,
    assume Hc : 0 ≤ c,
    show c * a ≤ c * b,
    proof
      have H1 : 0 ≤ b - a, from iff.elim_right !sub_nonneg_iff_le Hab,
      have H2 : 0 ≤ c * (b - a), from ordered_ring.mul_nonneg_of_nonneg_of_nonneg _ _ Hc H1,
      iff.mp !sub_nonneg_iff_le (!mul_sub_left_distrib ▸ H2)
    qed)
  (take a b c,
    assume Hab : a ≤ b,
    assume Hc : 0 ≤ c,
    show a * c ≤ b * c,
    proof
      have H1 : 0 ≤ b - a, from iff.elim_right !sub_nonneg_iff_le Hab,
      have H2 : 0 ≤ (b - a) * c, from ordered_ring.mul_nonneg_of_nonneg_of_nonneg _ _ H1 Hc,
      iff.mp !sub_nonneg_iff_le (!mul_sub_right_distrib ▸ H2)
    qed)
  (take a b c,
    assume Hab : a < b,
    assume Hc : 0 < c,
    show c * a < c * b,
    proof
      have H1 : 0 < b - a, from iff.elim_right !sub_pos_iff_lt Hab,
      have H2 : 0 < c * (b - a), from ordered_ring.mul_pos_of_pos_of_pos _ _ Hc H1,
      iff.mp !sub_pos_iff_lt (!mul_sub_left_distrib ▸ H2)
    qed)
  (take a b c,
    assume Hab : a < b,
    assume Hc : 0 < c,
    show a * c < b * c,
    proof
      have H1 : 0 < b - a, from iff.elim_right !sub_pos_iff_lt Hab,
      have H2 : 0 < (b - a) * c, from ordered_ring.mul_pos_of_pos_of_pos _ _ H1 Hc,
      iff.mp !sub_pos_iff_lt (!mul_sub_right_distrib ▸ H2)
    qed)

section

  variable [s : ordered_ring A]
  variables (a b c : A)
  include s

  -- TODO: remove after we short-circuit class-graph
  definition ordered_ring.to_mul [instance] [priority 100000] : has_mul A :=
  has_mul.mk (@ordered_ring.mul A s)
  definition ordered_ring.to_lt [instance] [priority 100000] : has_lt A :=
  has_lt.mk (@ordered_ring.lt A s)
  definition ordered_ring.to_zero [instance] [priority 100000] : has_zero A :=
  has_zero.mk (@ordered_ring.zero A s)

  theorem mul_le_mul_of_nonpos_left {a b c : A} (H : b ≤ a) (Hc : c ≤ 0) : c * a ≤ c * b :=
  have Hc' : -c ≥ 0, from iff.mp' !neg_nonneg_iff_nonpos Hc,
  have H1 : -c * b ≤ -c * a, from mul_le_mul_of_nonneg_left H Hc',
  have H2 : -(c * b) ≤ -(c * a), from !neg_mul_eq_neg_mul⁻¹ ▸ !neg_mul_eq_neg_mul⁻¹ ▸ H1,
  iff.mp !neg_le_neg_iff_le H2

  theorem mul_le_mul_of_nonpos_right {a b c : A} (H : b ≤ a) (Hc : c ≤ 0) : a * c ≤ b * c :=
  have Hc' : -c ≥ 0, from iff.mp' !neg_nonneg_iff_nonpos Hc,
  have H1 : b * -c ≤ a * -c, from mul_le_mul_of_nonneg_right H Hc',
  have H2 : -(b * c) ≤ -(a * c), from !neg_mul_eq_mul_neg⁻¹ ▸ !neg_mul_eq_mul_neg⁻¹ ▸ H1,
  iff.mp !neg_le_neg_iff_le H2

  theorem mul_nonneg_of_nonpos_of_nonpos {a b : A} (Ha : a ≤ 0) (Hb : b ≤ 0) : 0 ≤ a * b :=
  !zero_mul ▸ mul_le_mul_of_nonpos_right Ha Hb

  theorem mul_lt_mul_of_neg_left {a b c : A} (H : b < a) (Hc : c < 0) : c * a < c * b :=
  have Hc' : -c > 0, from iff.mp' !neg_pos_iff_neg Hc,
  have H1 : -c * b < -c * a, from mul_lt_mul_of_pos_left H Hc',
  have H2 : -(c * b) < -(c * a), from !neg_mul_eq_neg_mul⁻¹ ▸ !neg_mul_eq_neg_mul⁻¹ ▸ H1,
  iff.mp !neg_lt_neg_iff_lt H2

  theorem mul_lt_mul_of_neg_right {a b c : A} (H : b < a) (Hc : c < 0) : a * c < b * c :=
  have Hc' : -c > 0, from iff.mp' !neg_pos_iff_neg Hc,
  have H1 : b * -c < a * -c, from mul_lt_mul_of_pos_right H Hc',
  have H2 : -(b * c) < -(a * c), from !neg_mul_eq_mul_neg⁻¹ ▸ !neg_mul_eq_mul_neg⁻¹ ▸ H1,
  iff.mp !neg_lt_neg_iff_lt H2

  theorem mul_pos_of_neg_of_neg {a b : A} (Ha : a < 0) (Hb : b < 0) : 0 < a * b :=
  !zero_mul ▸ mul_lt_mul_of_neg_right Ha Hb

end

-- TODO: we can eliminate mul_pos_of_pos, but now it is not worth the effort to redeclare the class instance
structure linear_ordered_ring [class] (A : Type) extends ordered_ring A, linear_strong_order_pair A

-- TODO: after we break out definition of divides, show that this is an instance of integral domain,
--   i.e no zero divisors

section

  variable [s : linear_ordered_ring A]
  variables (a b c : A)
  include s

  theorem mul_self_nonneg : a * a ≥ 0 :=
  or.elim (le.total 0 a)
    (assume H : a ≥ 0, mul_nonneg_of_nonneg_of_nonneg H H)
    (assume H : a ≤ 0, mul_nonneg_of_nonpos_of_nonpos H H)

  theorem zero_le_one : 0 ≤ 1 := one_mul 1 ▸ mul_self_nonneg 1

  theorem zero_lt_one : 0 < 1 := lt_of_le_of_ne zero_le_one zero_ne_one

  -- TODO: move these to ordered_group.lean
  theorem lt_add_of_pos_right {a b : A} (H : b > 0) : a < a + b := !add_zero ▸ add_lt_add_left H a
  theorem lt_add_of_pos_left {a b : A} (H : b > 0) : a < b + a := !zero_add ▸ add_lt_add_right H a
  theorem le_add_of_nonneg_right {a b : A} (H : b ≥ 0) : a ≤ a + b := !add_zero ▸ add_le_add_left H a
  theorem le_add_of_nonneg_left {a b : A} (H : b ≥ 0) : a ≤ b + a := !zero_add ▸ add_le_add_right H a

  -- TODO: remove after we short-circuit class-graph
  definition linear_ordered_ring.to_mul [instance] [priority 100000] : has_mul A :=
  has_mul.mk (@linear_ordered_ring.mul A s)
  definition linear_ordered_ring.to_lt [instance] [priority 100000] : has_lt A :=
  has_lt.mk (@linear_ordered_ring.lt A s)
  definition linear_ordered_ring.to_zero [instance] [priority 100000] : has_zero A :=
  has_zero.mk (@linear_ordered_ring.zero A s)

  /- TODO: a good example of a performance bottleneck.

  Without any of the "proof ... qed" pairs, it exceeds the unifier maximum number of steps.

  It works with at least one "proof ... qed", but takes about two seconds on my laptop. I do not
  know where the bottleneck is.

  Adding the explicit arguments to lt_or_eq_or_lt_cases does not seem to help at all. (The proof
    still works if all the instances are replaced by "lt_or_eq_or_lt_cases" alone.)

  Adding an extra "proof ... qed" around "!mul_zero ▸ Hb⁻¹ ▸ Hab" fails with "value has
  metavariables". I am not sure why.
  -/
  theorem pos_and_pos_or_neg_and_neg_of_mul_pos (Hab : a * b > 0) :
    (a > 0 ∧ b > 0) ∨ (a < 0 ∧ b < 0) :=
  lt_or_eq_or_lt_cases
    (assume Ha : 0 < a,
      lt_or_eq_or_lt_cases
        (assume Hb : 0 < b, or.inl (and.intro Ha Hb))
        (assume Hb : 0 = b,
          absurd (!mul_zero ▸ Hb⁻¹ ▸ Hab) (lt.irrefl 0))
        (assume Hb : b < 0,
          absurd Hab (not_lt_of_lt (mul_neg_of_pos_of_neg Ha Hb))))
    (assume Ha : 0 = a,
      absurd (!zero_mul ▸ Ha⁻¹ ▸ Hab) (lt.irrefl 0))
    (assume Ha : a < 0,
      lt_or_eq_or_lt_cases
        (assume Hb : 0 < b,
          absurd Hab (not_lt_of_lt (mul_neg_of_neg_of_pos Ha Hb)))
        (assume Hb : 0 = b,
          absurd (!mul_zero ▸ Hb⁻¹ ▸ Hab) (lt.irrefl 0))
        (assume Hb : b < 0, or.inr (and.intro Ha Hb)))

  set_option pp.coercions true
  set_option pp.implicit true
  set_option pp.notation false
  -- print definition pos_and_pos_or_neg_and_neg_of_mul_pos

  -- TODO: use previous and integral domain
  theorem noneg_and_nonneg_or_nonpos_and_nonpos_of_mul_nonneg (Hab : a * b ≥ 0) :
    (a ≥ 0 ∧ b ≥ 0) ∨ (a ≤ 0 ∧ b ≤ 0) :=
  sorry

end

/-
  Still left to do:

  Isabelle's library has all kinds of cancelation rules for the simplifier, search on
    mult_le_cancel_right1 in Rings.thy.

  Properties of abs, sgn, and dvd.

  Multiplication and one, starting with mult_right_le_one_le.
-/

structure linear_ordered_comm_ring [class] (A : Type) extends linear_ordered_ring A, comm_monoid A

end algebra
