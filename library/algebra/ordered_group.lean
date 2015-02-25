/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: algebra.ordered_group
Authors: Jeremy Avigad

Partially ordered additive groups, modeled on Isabelle's library. We could refine the structures,
but we would have to declare more inheritance paths.
-/

import logic.eq data.unit data.sigma data.prod
import algebra.function algebra.binary
import algebra.group algebra.order
open eq eq.ops   -- note: ⁻¹ will be overloaded

namespace algebra

variable {A : Type}

/- partially ordered monoids, such as the natural numbers -/

structure ordered_cancel_comm_monoid [class] (A : Type) extends add_comm_monoid A,
  add_left_cancel_semigroup A, add_right_cancel_semigroup A, order_pair A :=
(add_le_add_left : ∀a b, le a b → ∀c, le (add c a) (add c b))
(le_of_add_le_add_left : ∀a b c, le (add a b) (add a c) → le b c)

section
  variables [s : ordered_cancel_comm_monoid A]
  variables {a b c d e : A}
  include s

  theorem add_le_add_left (H : a ≤ b) (c : A) : c + a ≤ c + b :=
  !ordered_cancel_comm_monoid.add_le_add_left H c

  theorem add_le_add_right (H : a ≤ b) (c : A) : a + c ≤ b + c :=
  (add.comm c a) ▸ (add.comm c b) ▸ (add_le_add_left H c)

  theorem add_le_add (Hab : a ≤ b) (Hcd : c ≤ d) : a + c ≤ b + d :=
  le.trans (add_le_add_right Hab c) (add_le_add_left Hcd b)

  theorem add_lt_add_left (H : a < b) (c : A) : c + a < c + b :=
  have H1 : c + a ≤ c + b, from add_le_add_left (le_of_lt H) c,
  have H2 : c + a ≠ c + b, from
    take H3 : c + a = c + b,
    have H4 : a = b, from add.left_cancel H3,
    ne_of_lt H H4,
  lt_of_le_of_ne H1 H2

  theorem add_lt_add_right (H : a < b) (c : A) : a + c < b + c :=
  (add.comm c a) ▸ (add.comm c b) ▸ (add_lt_add_left H c)

  theorem le_add_of_nonneg_right (H : b ≥ 0) : a ≤ a + b :=
    !add_zero ▸ add_le_add_left H a

  theorem le_add_of_nonneg_left (H : b ≥ 0) : a ≤ b + a :=
    !zero_add ▸ add_le_add_right H a

  theorem add_lt_add (Hab : a < b) (Hcd : c < d) : a + c < b + d :=
  lt.trans (add_lt_add_right Hab c) (add_lt_add_left Hcd b)

  theorem add_lt_add_of_le_of_lt (Hab : a ≤ b) (Hcd : c < d) : a + c < b + d :=
  lt_of_le_of_lt (add_le_add_right Hab c) (add_lt_add_left Hcd b)

  theorem add_lt_add_of_lt_of_le (Hab : a < b) (Hcd : c ≤ d) : a + c < b + d :=
  lt_of_lt_of_le (add_lt_add_right Hab c) (add_le_add_left Hcd b)

  theorem lt_add_of_pos_right (H : b > 0) : a < a + b := !add_zero ▸ add_lt_add_left H a

  theorem lt_add_of_pos_left (H : b > 0) : a < b + a := !zero_add ▸ add_lt_add_right H a

  -- here we start using le_of_add_le_add_left.
  theorem le_of_add_le_add_left (H : a + b ≤ a + c) : b ≤ c :=
  !ordered_cancel_comm_monoid.le_of_add_le_add_left H

  theorem le_of_add_le_add_right (H : a + b ≤ c + b) : a ≤ c :=
  le_of_add_le_add_left ((add.comm a b) ▸ (add.comm c b) ▸ H)

  theorem lt_of_add_lt_add_left (H : a + b < a + c) : b < c :=
  have H1 : b ≤ c, from le_of_add_le_add_left (le_of_lt H),
  have H2 : b ≠ c, from
    assume H3 : b = c, lt.irrefl _ (H3 ▸ H),
  lt_of_le_of_ne H1 H2

  theorem lt_of_add_lt_add_right (H : a + b < c + b) : a < c :=
  lt_of_add_lt_add_left ((add.comm a b) ▸ (add.comm c b) ▸ H)

  theorem add_le_add_left_iff (a b c : A) : a + b ≤ a + c ↔ b ≤ c :=
  iff.intro le_of_add_le_add_left (assume H, add_le_add_left H _)

  theorem add_le_add_right_iff (a b c : A) : a + b ≤ c + b ↔ a ≤ c :=
  iff.intro le_of_add_le_add_right (assume H, add_le_add_right H _)

  theorem add_lt_add_left_iff (a b c : A) : a + b < a + c ↔ b < c :=
  iff.intro lt_of_add_lt_add_left (assume H, add_lt_add_left H _)

  theorem add_lt_add_right_iff (a b c : A) : a + b < c + b ↔ a < c :=
  iff.intro lt_of_add_lt_add_right (assume H, add_lt_add_right H _)

  -- here we start using properties of zero.
  theorem add_nonneg (Ha : 0 ≤ a) (Hb : 0 ≤ b) : 0 ≤ a + b :=
  !zero_add ▸ (add_le_add Ha Hb)

  theorem add_pos (Ha : 0 < a) (Hb : 0 < b) : 0 < a + b :=
  !zero_add ▸ (add_lt_add Ha Hb)

  theorem add_pos_of_pos_of_nonneg (Ha : 0 < a) (Hb : 0 ≤ b) : 0 < a + b :=
  !zero_add ▸ (add_lt_add_of_lt_of_le Ha Hb)

  theorem add_pos_of_nonneg_of_pos (Ha : 0 ≤ a) (Hb : 0 < b) : 0 < a + b :=
  !zero_add ▸ (add_lt_add_of_le_of_lt Ha Hb)

  theorem add_nonpos (Ha : a ≤ 0) (Hb : b ≤ 0) : a + b ≤ 0 :=
  !zero_add ▸ (add_le_add Ha Hb)

  theorem add_neg (Ha : a < 0) (Hb : b < 0) : a + b < 0 :=
  !zero_add ▸ (add_lt_add Ha Hb)

  theorem add_neg_of_neg_of_nonpos (Ha : a < 0) (Hb : b ≤ 0) : a + b < 0 :=
  !zero_add ▸ (add_lt_add_of_lt_of_le Ha Hb)

  theorem add_neg_of_nonpos_of_neg (Ha : a ≤ 0) (Hb : b < 0) : a + b < 0 :=
  !zero_add ▸ (add_lt_add_of_le_of_lt Ha Hb)

  -- TODO: add nonpos version (will be easier with simplifier)
  theorem add_eq_zero_iff_eq_zero_and_eq_zero_of_nonneg_of_nonneg
    (Ha : 0 ≤ a) (Hb : 0 ≤ b) : a + b = 0 ↔ a = 0 ∧ b = 0 :=
  iff.intro
    (assume Hab : a + b = 0,
      have Ha' : a ≤ 0, from
        calc
          a = a + 0 : add_zero
            ... ≤ a + b : add_le_add_left Hb
            ... = 0 : Hab,
      have Haz : a = 0, from le.antisymm Ha' Ha,
      have Hb' : b ≤ 0, from
        calc
          b = 0 + b : zero_add
            ... ≤ a + b : add_le_add_right Ha
            ... = 0 : Hab,
      have Hbz : b = 0, from le.antisymm Hb' Hb,
      and.intro Haz Hbz)
    (assume Hab : a = 0 ∧ b = 0,
      and.elim Hab (λ Ha Hb, by rewrite [Ha, Hb, add_zero]))

  theorem le_add_of_nonneg_of_le (Ha : 0 ≤ a) (Hbc : b ≤ c) : b ≤ a + c :=
  !zero_add ▸ add_le_add Ha Hbc

  theorem le_add_of_le_of_nonneg (Hbc : b ≤ c) (Ha : 0 ≤ a) : b ≤ c + a :=
  !add_zero ▸ add_le_add Hbc Ha

  theorem lt_add_of_pos_of_le (Ha : 0 < a) (Hbc : b ≤ c) : b < a + c :=
  !zero_add ▸ add_lt_add_of_lt_of_le Ha Hbc

  theorem lt_add_of_le_of_pos (Hbc : b ≤ c) (Ha : 0 < a) : b < c + a :=
  !add_zero ▸ add_lt_add_of_le_of_lt Hbc Ha

  theorem add_le_of_nonpos_of_le (Ha : a ≤ 0) (Hbc : b ≤ c) : a + b ≤ c :=
  !zero_add ▸ add_le_add Ha Hbc

  theorem add_le_of_le_of_nonpos (Hbc : b ≤ c) (Ha : a ≤ 0) : b + a ≤ c :=
  !add_zero ▸ add_le_add Hbc Ha

  theorem add_lt_of_neg_of_le (Ha : a < 0) (Hbc : b ≤ c) : a + b < c :=
  !zero_add ▸ add_lt_add_of_lt_of_le Ha Hbc

  theorem add_lt_of_le_of_neg (Hbc : b ≤ c) (Ha : a < 0) : b + a < c :=
  !add_zero ▸ add_lt_add_of_le_of_lt Hbc Ha

  theorem lt_add_of_nonneg_of_lt (Ha : 0 ≤ a) (Hbc : b < c) : b < a + c :=
  !zero_add ▸ add_lt_add_of_le_of_lt Ha Hbc

  theorem lt_add_of_lt_of_nonneg (Hbc : b < c) (Ha : 0 ≤ a) : b < c + a :=
  !add_zero ▸ add_lt_add_of_lt_of_le Hbc Ha

  theorem lt_add_of_pos_of_lt (Ha : 0 < a) (Hbc : b < c) : b < a + c :=
  !zero_add ▸ add_lt_add Ha Hbc

  theorem lt_add_of_lt_of_pos (Hbc : b < c) (Ha : 0 < a) : b < c + a :=
  !add_zero ▸ add_lt_add Hbc Ha

  theorem add_lt_of_nonpos_of_lt (Ha : a ≤ 0) (Hbc : b < c) : a + b < c :=
  !zero_add ▸ add_lt_add_of_le_of_lt Ha Hbc

  theorem add_lt_of_lt_of_nonpos (Hbc : b < c) (Ha : a ≤ 0)  : b + a < c :=
  !add_zero ▸ add_lt_add_of_lt_of_le Hbc Ha

  theorem add_lt_of_neg_of_lt (Ha : a < 0) (Hbc : b < c) : a + b < c :=
  !zero_add ▸ add_lt_add Ha Hbc

  theorem add_lt_of_lt_of_neg (Hbc : b < c) (Ha : a < 0) : b + a < c :=
  !add_zero ▸ add_lt_add Hbc Ha
end

-- TODO: add properties of max and min

/- partially ordered groups -/

structure ordered_comm_group [class] (A : Type) extends add_comm_group A, order_pair A :=
(add_le_add_left : ∀a b, le a b → ∀c, le (add c a) (add c b))

theorem ordered_comm_group.le_of_add_le_add_left [s : ordered_comm_group A] {a b c : A} (H : a + b ≤ a + c) : b ≤ c :=
have H' [visible] : -a + (a + b) ≤ -a + (a + c), from ordered_comm_group.add_le_add_left _ _ H _,
by rewrite *neg_add_cancel_left at H'; exact H'

definition ordered_comm_group.to_ordered_cancel_comm_monoid [instance] [coercion] [reducible]
    [s : ordered_comm_group A] : ordered_cancel_comm_monoid A :=
⦃ ordered_cancel_comm_monoid, s,
  add_left_cancel       := @add.left_cancel A s,
  add_right_cancel      := @add.right_cancel A s,
  le_of_add_le_add_left := @ordered_comm_group.le_of_add_le_add_left A s ⦄

section
  variables [s : ordered_comm_group A] (a b c d e : A)
  include s

  theorem neg_le_neg {a b : A} (H : a ≤ b) : -b ≤ -a :=
  have H1 : 0 ≤ -a + b, from !add.left_inv ▸ !(add_le_add_left H),
  !add_neg_cancel_right ▸ !zero_add ▸ add_le_add_right H1 (-b)

  theorem le_of_neg_le_neg {a b : A} (H : -b ≤ -a) : a ≤ b :=
  neg_neg a ▸ neg_neg b ▸ neg_le_neg H

  theorem neg_le_neg_iff_le : -a ≤ -b ↔ b ≤ a :=
  iff.intro le_of_neg_le_neg neg_le_neg

  theorem nonneg_of_neg_nonpos {a : A} (H : -a ≤ 0) : 0 ≤ a :=
  le_of_neg_le_neg (neg_zero⁻¹ ▸ H)

  theorem neg_nonpos_of_nonneg {a : A} (H : 0 ≤ a) : -a ≤ 0 :=
  neg_zero ▸ neg_le_neg H

  theorem neg_nonpos_iff_nonneg : -a ≤ 0 ↔ 0 ≤ a :=
  iff.intro nonneg_of_neg_nonpos neg_nonpos_of_nonneg

  theorem nonpos_of_neg_nonneg {a : A} (H : 0 ≤ -a) : a ≤ 0 :=
  le_of_neg_le_neg (neg_zero⁻¹ ▸ H)

  theorem neg_nonneg_of_nonpos {a : A} (H : a ≤ 0) : 0 ≤ -a :=
  neg_zero ▸ neg_le_neg H

  theorem neg_nonneg_iff_nonpos : 0 ≤ -a ↔ a ≤ 0 :=
  iff.intro nonpos_of_neg_nonneg neg_nonneg_of_nonpos

  theorem neg_lt_neg {a b : A} (H : a < b) : -b < -a :=
  have H1 : 0 < -a + b, from !add.left_inv ▸ !(add_lt_add_left H),
  !add_neg_cancel_right ▸ !zero_add ▸ add_lt_add_right H1 (-b)

  theorem lt_of_neg_lt_neg {a b : A} (H : -b < -a) : a < b :=
  neg_neg a ▸ neg_neg b ▸ neg_lt_neg H

  theorem neg_lt_neg_iff_lt : -a < -b ↔ b < a :=
  iff.intro lt_of_neg_lt_neg neg_lt_neg

  theorem pos_of_neg_neg {a : A} (H : -a < 0) : 0 < a :=
  lt_of_neg_lt_neg (neg_zero⁻¹ ▸ H)

  theorem neg_neg_of_pos {a : A} (H : 0 < a) : -a < 0 :=
  neg_zero ▸ neg_lt_neg H

  theorem neg_neg_iff_pos : -a < 0 ↔ 0 < a :=
  iff.intro pos_of_neg_neg neg_neg_of_pos

  theorem neg_of_neg_pos {a : A} (H : 0 < -a) : a < 0 :=
  lt_of_neg_lt_neg (neg_zero⁻¹ ▸ H)

  theorem neg_pos_of_neg {a : A} (H : a < 0) : 0 < -a :=
  neg_zero ▸ neg_lt_neg H

  theorem neg_pos_iff_neg : 0 < -a ↔ a < 0 :=
  iff.intro neg_of_neg_pos neg_pos_of_neg

  theorem le_neg_iff_le_neg : a ≤ -b ↔ b ≤ -a := !neg_neg ▸ !neg_le_neg_iff_le

  theorem neg_le_iff_neg_le : -a ≤ b ↔ -b ≤ a := !neg_neg ▸ !neg_le_neg_iff_le

  theorem lt_neg_iff_lt_neg : a < -b ↔ b < -a := !neg_neg ▸ !neg_lt_neg_iff_lt

  theorem neg_lt_iff_neg_lt : -a < b ↔ -b < a := !neg_neg ▸ !neg_lt_neg_iff_lt

  theorem sub_nonneg_iff_le : 0 ≤ a - b ↔ b ≤ a := !sub_self ▸ !add_le_add_right_iff

  theorem sub_nonpos_iff_le : a - b ≤ 0 ↔ a ≤ b := !sub_self ▸ !add_le_add_right_iff

  theorem sub_pos_iff_lt : 0 < a - b ↔ b < a := !sub_self ▸ !add_lt_add_right_iff

  theorem sub_neg_iff_lt : a - b < 0 ↔ a < b := !sub_self ▸ !add_lt_add_right_iff

  theorem add_le_iff_le_neg_add : a + b ≤ c ↔ b ≤ -a + c :=
  have H: a + b ≤ c ↔ -a + (a + b) ≤ -a + c, from iff.symm (!add_le_add_left_iff),
  !neg_add_cancel_left ▸ H

  theorem add_le_iff_le_sub_left : a + b ≤ c ↔ b ≤ c - a :=
  !add.comm ▸ !add_le_iff_le_neg_add

  theorem add_le_iff_le_sub_right : a + b ≤ c ↔ a ≤ c - b :=
  have H: a + b ≤ c ↔ a + b - b ≤ c - b, from iff.symm (!add_le_add_right_iff),
  !add_neg_cancel_right ▸ H

  theorem le_add_iff_neg_add_le : a ≤ b + c ↔ -b + a ≤ c :=
  have H: a ≤ b + c ↔ -b + a ≤ -b + (b + c), from iff.symm (!add_le_add_left_iff),
  !neg_add_cancel_left ▸ H

  theorem le_add_iff_sub_left_le : a ≤ b + c ↔ a - b ≤ c :=
  !add.comm ▸ !le_add_iff_neg_add_le

  theorem le_add_iff_sub_right_le : a ≤ b + c ↔ a - c ≤ b :=
  have H: a ≤ b + c ↔ a - c ≤ b + c - c, from iff.symm (!add_le_add_right_iff),
  !add_neg_cancel_right ▸ H

  theorem add_lt_iff_lt_neg_add_left : a + b < c ↔ b < -a + c :=
  have H: a + b < c ↔ -a + (a + b) < -a + c, from iff.symm (!add_lt_add_left_iff),
  !neg_add_cancel_left ▸ H

  theorem add_lt_iff_lt_neg_add_right : a + b < c ↔ a < -b + c :=
  !add.comm ▸ !add_lt_iff_lt_neg_add_left

  theorem add_lt_iff_lt_sub_left : a + b < c ↔ b < c - a :=
  !add.comm ▸ !add_lt_iff_lt_neg_add_left

  theorem add_lt_add_iff_lt_sub_right : a + b < c ↔ a < c - b :=
  have H: a + b < c ↔ a + b - b < c - b, from iff.symm (!add_lt_add_right_iff),
  !add_neg_cancel_right ▸ H

  theorem lt_add_iff_neg_add_lt_left : a < b + c ↔ -b + a < c :=
  have H: a < b + c ↔ -b + a < -b + (b + c), from iff.symm (!add_lt_add_left_iff),
  !neg_add_cancel_left ▸ H

  theorem lt_add_iff_neg_add_lt_right : a < b + c ↔ -c + a < b :=
  !add.comm ▸ !lt_add_iff_neg_add_lt_left

  theorem lt_add_iff_sub_lt_left : a < b + c ↔ a - b < c :=
  !add.comm ▸ !lt_add_iff_neg_add_lt_left

  theorem lt_add_iff_sub_lt_right : a < b + c ↔ a - c < b :=
  !add.comm ▸ !lt_add_iff_sub_lt_left

  -- TODO: the Isabelle library has varations on a + b ≤ b ↔ a ≤ 0

  theorem le_iff_le_of_sub_eq_sub {a b c d : A} (H : a - b = c - d) : a ≤ b ↔ c ≤ d :=
  calc
    a ≤ b ↔ a - b ≤ 0 : iff.symm (sub_nonpos_iff_le a b)
      ... ↔ c - d ≤ 0 : H ▸ !iff.refl
      ... ↔ c ≤ d : sub_nonpos_iff_le c d

  theorem lt_iff_lt_of_sub_eq_sub {a b c d : A} (H : a - b = c - d) : a < b ↔ c < d :=
  calc
    a < b ↔ a - b < 0 : iff.symm (sub_neg_iff_lt a b)
      ... ↔ c - d < 0 : H ▸ !iff.refl
      ... ↔ c < d : sub_neg_iff_lt c d

  theorem sub_le_sub_left {a b : A} (H : a ≤ b) (c : A) : c - b ≤ c - a :=
  add_le_add_left (neg_le_neg H) c

  theorem sub_le_sub_right {a b : A} (H : a ≤ b) (c : A) : a - c ≤ b - c := add_le_add_right H (-c)

  theorem sub_le_sub {a b c d : A} (Hab : a ≤ b) (Hcd : c ≤ d) : a - d ≤ b - c :=
  add_le_add Hab (neg_le_neg Hcd)

  theorem sub_lt_sub_left {a b : A} (H : a < b) (c : A) : c - b < c - a :=
  add_lt_add_left (neg_lt_neg H) c

  theorem sub_lt_sub_right {a b : A} (H : a < b) (c : A) : a - c < b - c := add_lt_add_right H (-c)

  theorem sub_lt_sub {a b c d : A} (Hab : a < b) (Hcd : c < d) : a - d < b - c :=
  add_lt_add Hab (neg_lt_neg Hcd)

  theorem sub_lt_sub_of_le_of_lt {a b c d : A} (Hab : a ≤ b) (Hcd : c < d) : a - d < b - c :=
  add_lt_add_of_le_of_lt Hab (neg_lt_neg Hcd)

  theorem sub_lt_sub_of_lt_of_le {a b c d : A} (Hab : a < b) (Hcd : c ≤ d) : a - d < b - c :=
  add_lt_add_of_lt_of_le Hab (neg_le_neg Hcd)

  theorem sub_le_self (a : A) {b : A} (H : b ≥ 0) : a - b ≤ a :=
  calc
    a - b = a + -b : rfl
      ... ≤ a + 0  : add_le_add_left (neg_nonpos_of_nonneg H)
      ... = a      : add_zero

  theorem sub_lt_self (a : A) {b : A} (H : b > 0) : a - b < a :=
  calc
    a - b = a + -b : rfl
      ... < a + 0  : add_lt_add_left (neg_neg_of_pos H)
      ... = a      : add_zero
end

structure decidable_linear_ordered_comm_group [class] (A : Type)
    extends ordered_comm_group A, decidable_linear_order A

section
  variables [s : decidable_linear_ordered_comm_group A]
  variables {a b c d e : A}
  include s

  theorem eq_zero_of_neg_eq (H : -a = a) : a = 0 :=
  lt.by_cases
    (assume H1 : a < 0,
      have H2: a > 0, from H ▸ neg_pos_of_neg H1,
      absurd H1 (lt.asymm H2))
    (assume H1 : a = 0, H1)
    (assume H1 : a > 0,
      have H2: a < 0, from H ▸ neg_neg_of_pos H1,
      absurd H1 (lt.asymm H2))

  definition abs (a : A) : A := if 0 ≤ a then a else -a

  notation `|` a `|` := abs a

  theorem abs_of_nonneg (H : a ≥ 0) : |a| = a := if_pos H

  theorem abs_of_pos (H : a > 0) : |a| = a := if_pos (le_of_lt H)

  theorem abs_of_neg (H : a < 0) : |a| = -a := if_neg (not_le_of_lt H)

  theorem abs_zero : |0| = 0 := abs_of_nonneg (le.refl _)

  theorem abs_of_nonpos (H : a ≤ 0) : |a| = -a :=
  decidable.by_cases
    (assume H1 : a = 0, by rewrite [H1, abs_zero, neg_zero])
    (assume H1 : a ≠ 0,
      have H2 : a < 0, from lt_of_le_of_ne H H1,
      abs_of_neg H2)

  theorem abs_neg (a : A) : |-a| = |a| :=
  or.elim (le.total 0 a)
    (assume H1 : 0 ≤ a, by rewrite [abs_of_nonpos (neg_nonpos_of_nonneg H1), neg_neg, abs_of_nonneg H1])
    (assume H1 : a ≤ 0, by rewrite [abs_of_nonneg (neg_nonneg_of_nonpos H1), abs_of_nonpos H1])

  theorem abs_nonneg (a : A) : | a | ≥ 0 :=
  or.elim (le.total 0 a)
    (assume H : 0 ≤ a, by rewrite (abs_of_nonneg H); exact H)
    (assume H : a ≤ 0,
      calc
          0 ≤ -a  : neg_nonneg_of_nonpos H
        ... = |a| : abs_of_nonpos H)

  theorem abs_abs (a : A) : | |a| | = |a| := abs_of_nonneg !abs_nonneg

  theorem le_abs_self (a : A) : a ≤ |a| :=
  or.elim (le.total 0 a)
    (assume H : 0 ≤ a, abs_of_nonneg H ▸ !le.refl)
    (assume H : a ≤ 0, le.trans H !abs_nonneg)

  theorem neg_le_abs_self (a : A) : -a ≤ |a| :=
  !abs_neg ▸ !le_abs_self

  theorem eq_zero_of_abs_eq_zero (H : |a| = 0) : a = 0 :=
  have H1 : a ≤ 0, from H ▸ le_abs_self a,
  have H2 : -a ≤ 0, from H ▸ abs_neg a ▸ le_abs_self (-a),
  le.antisymm H1 (nonneg_of_neg_nonpos H2)

  theorem abs_eq_zero_iff_eq_zero (a : A) : |a| = 0 ↔ a = 0 :=
  iff.intro eq_zero_of_abs_eq_zero (assume H, congr_arg abs H ⬝ !abs_zero)

  theorem abs_pos_of_pos (H : a > 0) : |a| > 0 :=
  (abs_of_pos H)⁻¹ ▸ H

  theorem abs_pos_of_neg (H : a < 0) : |a| > 0 :=
  !abs_neg ▸ abs_pos_of_pos (neg_pos_of_neg H)

  theorem abs_pos_of_ne_zero (H : a ≠ 0) : |a| > 0 :=
  or.elim (lt_or_gt_of_ne H) abs_pos_of_neg abs_pos_of_pos

  theorem abs_sub (a b : A) : |a - b| = |b - a| :=
  by rewrite [-neg_sub, abs_neg]

  theorem abs.by_cases {P : A → Prop} {a : A} (H1 : P a) (H2 : P (-a)) : P |a| :=
  or.elim (le.total 0 a)
    (assume H : 0 ≤ a, (abs_of_nonneg H)⁻¹ ▸ H1)
    (assume H : a ≤ 0, (abs_of_nonpos H)⁻¹ ▸ H2)

  theorem abs_le_of_le_of_neg_le (H1 : a ≤ b) (H2 : -a ≤ b) : |a| ≤ b :=
  abs.by_cases H1 H2

  theorem abs_lt_of_lt_of_neg_lt (H1 : a < b) (H2 : -a < b) : |a| < b :=
  abs.by_cases H1 H2

  -- the triangle inequality
  context
    private lemma aux1 {a b : A} (H1 : a + b ≥ 0) (H2 : a ≥ 0) : |a + b| ≤ |a| + |b| :=
    decidable.by_cases
      (assume H3 : b ≥ 0,
          calc
            |a + b| ≤ |a + b|   : le.refl
                ... = a + b     : abs_of_nonneg H1
                ... = |a| + b   : abs_of_nonneg H2
                ... = |a| + |b| : abs_of_nonneg H3)
      (assume H3 : ¬ b ≥ 0,
        have H4 : b ≤ 0, from le_of_lt (lt_of_not_le H3),
        calc
          |a + b| = a + b     : abs_of_nonneg H1
              ... = |a| + b   : abs_of_nonneg H2
              ... ≤ |a| + 0   : add_le_add_left H4
              ... ≤ |a| + -b  : add_le_add_left (neg_nonneg_of_nonpos H4)
              ... = |a| + |b| : abs_of_nonpos H4)

    private lemma aux2 {a b : A} (H1 : a + b ≥ 0) : |a + b| ≤ |a| + |b| :=
    or.elim (le.total b 0)
      (assume H2 : b ≤ 0,
        have H3 : ¬ a < 0, from
          assume H4 : a < 0,
          have H5 : a + b < 0, from !add_zero ▸ add_lt_add_of_lt_of_le H4 H2,
          not_lt_of_le H1 H5,
        aux1 H1 (le_of_not_lt H3))
      (assume H2 : 0 ≤ b,
        have H3 : |b + a| ≤ |b| + |a|, from aux1 (add.comm a b ▸ H1) H2,
        add.comm b a ▸ (add.comm |b| |a|) ▸ H3)

    theorem abs_add_le_abs_add_abs (a b : A) : |a + b| ≤ |a| + |b| :=
    or.elim (le.total 0 (a + b))
      (assume H2 : 0 ≤ a + b, aux2 H2)
      (assume H2 : a + b ≤ 0,
        have H3 : -a + -b = -(a + b), by rewrite neg_add,
        have H4 : -(a + b) ≥ 0, from iff.mp' (neg_nonneg_iff_nonpos (a+b)) H2,
        calc
          |a + b| = |-a + -b|   : by rewrite [-abs_neg, neg_add]
              ... ≤ |-a| + |-b| : aux2 (H3⁻¹ ▸ H4)
              ... = |a| + |b|   : by rewrite *abs_neg)
  end

  theorem abs_sub_abs_le_abs_sub (a b : A) : |a| - |b| ≤ |a - b| :=
  have H1 : |a| - |b| + |b| ≤ |a - b| + |b|, from
    calc
      |a| - |b| + |b| = |a| : sub_add_cancel
        ... = |a - b + b|   : sub_add_cancel
        ... ≤ |a - b| + |b| : algebra.abs_add_le_abs_add_abs,
  algebra.le_of_add_le_add_right H1
end

end algebra
