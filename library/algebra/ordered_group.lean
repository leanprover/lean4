/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: algebra.ordered_group
Authors: Jeremy Avigad

Partially ordered additive groups. Modeled on Isabelle's library. The comments below indicate that
we could refine the structures, though we would have to declare more inheritance paths.
-/

import logic.eq data.unit data.sigma data.prod
import algebra.function algebra.binary
import algebra.group algebra.order

open eq eq.ops   -- note: ⁻¹ will be overloaded

namespace algebra

variable {A : Type}

structure ordered_cancel_comm_monoid [class] (A : Type) extends add_comm_monoid A,
  add_left_cancel_semigroup A, add_right_cancel_semigroup A, order_pair A :=
(add_le_add_left : ∀a b, le a b → ∀c, le (add c a) (add c b))
(le_of_add_le_add_left : ∀a b c, le (add a b) (add a c) → le b c)

section

  variables [s : ordered_cancel_comm_monoid A] (a b c d e : A)
  include s

  theorem add_le_add_left {a b : A} (H : a ≤ b) (c : A) : c + a ≤ c + b :=
  !ordered_cancel_comm_monoid.add_le_add_left H c

  theorem add_le_add_right {a b : A} (H : a ≤ b) (c : A) : a + c ≤ b + c :=
  (add.comm c a) ▸ (add.comm c b) ▸ (add_le_add_left H c)

  theorem add_le_add {a b c d : A} (Hab : a ≤ b) (Hcd : c ≤ d) : a + c ≤ b + d :=
  le.trans (add_le_add_right Hab c) (add_le_add_left Hcd b)

  theorem add_lt_add_left {a b : A} (H : a < b) (c : A) : c + a < c + b :=
  have H1 : c + a ≤ c + b, from add_le_add_left (le_of_lt H) c,
  have H2 : c + a ≠ c + b, from
    take H3 : c + a = c + b,
    have H4 : a = b, from add.left_cancel H3,
    lt.ne H H4,
  lt_of_le_of_ne H1 H2

  theorem add_lt_add_right {a b : A} (H : a < b) (c : A) : a + c < b + c :=
  (add.comm c a) ▸ (add.comm c b) ▸ (add_lt_add_left H c)

  theorem add_lt_add_of_lt_of_lt {a b c d : A} (Hab : a < b) (Hcd : c < d) : a + c < b + d :=
  lt.trans (add_lt_add_right Hab c) (add_lt_add_left Hcd b)

  theorem add_lt_add_of_le_of_lt {a b c d : A} (Hab : a ≤ b) (Hcd : c < d) : a + c < b + d :=
  lt_of_le_of_lt (add_le_add_right Hab c) (add_lt_add_left Hcd b)

  theorem add_lt_add_of_lt_of_le {a b c d : A} (Hab : a < b) (Hcd : c ≤ d) : a + c < b + d :=
  lt_of_lt_of_le (add_lt_add_right Hab c) (add_le_add_left Hcd b)

  -- here we start using le_of_add_le_add_left.
  theorem le_of_add_le_add_left {a b c : A} (H : a + b ≤ a + c) : b ≤ c :=
  !ordered_cancel_comm_monoid.le_of_add_le_add_left H

  theorem le_of_add_le_add_right {a b c : A} (H : a + b ≤ c + b) : a ≤ c :=
  le_of_add_le_add_left ((add.comm a b) ▸ (add.comm c b) ▸ H)

  theorem lt_of_add_lt_add_left {a b c : A} (H : a + b < a + c) : b < c :=
  have H1 : b ≤ c, from le_of_add_le_add_left (le_of_lt H),
  have H2 : b ≠ c, from
    assume H3 : b = c, lt.irrefl _ (H3 ▸ H),
  lt_of_le_of_ne H1 H2

  theorem lt_of_add_lt_add_right {a b c : A} (H : a + b < c + b) : a < c :=
  lt_of_add_lt_add_left ((add.comm a b) ▸ (add.comm c b) ▸ H)

  theorem add_le_add_left_iff : a + b ≤ a + c ↔ b ≤ c :=
  iff.intro le_of_add_le_add_left (assume H, add_le_add_left H _)

  theorem add_le_add_right_iff : a + b ≤ c + b ↔ a ≤ c :=
  iff.intro le_of_add_le_add_right (assume H, add_le_add_right H _)

  theorem add_lt_add_left_iff : a + b < a + c ↔ b < c :=
  iff.intro lt_of_add_lt_add_left (assume H, add_lt_add_left H _)

  theorem add_lt_add_right_iff : a + b < c + b ↔ a < c :=
  iff.intro lt_of_add_lt_add_right (assume H, add_lt_add_right H _)

  -- here we start using properties of zero.
  theorem add_nonneg {a b : A} (Ha : 0 ≤ a) (Hb : 0 ≤ b) : 0 ≤ a + b :=
  !add.left_id ▸ (add_le_add Ha Hb)

  theorem add_pos_of_pos_of_nonneg {a b : A} (Ha : 0 < a) (Hb : 0 ≤ b) : 0 < a + b :=
  !add.left_id ▸ (add_lt_add_of_lt_of_le Ha Hb)

  theorem add_pos_of_nonneg_of_pos {a b : A} (Ha : 0 ≤ a) (Hb : 0 < b) : 0 < a + b :=
  !add.left_id ▸ (add_lt_add_of_le_of_lt Ha Hb)

  theorem add_pos_of_pos_of_pos {a b : A} (Ha : 0 < a) (Hb : 0 < b) : 0 < a + b :=
  !add.left_id ▸ (add_lt_add_of_lt_of_lt Ha Hb)

  theorem add_nonpos {a b : A} (Ha : a ≤ 0) (Hb : b ≤ 0) : a + b ≤ 0 :=
  !add.left_id ▸ (add_le_add Ha Hb)

  theorem add_neg_of_neg_of_nonpos {a b : A} (Ha : a < 0) (Hb : b ≤ 0) : a + b < 0 :=
  !add.left_id ▸ (add_lt_add_of_lt_of_le Ha Hb)

  theorem add_neg_of_nonpos_of_neg {a b : A} (Ha : a ≤ 0) (Hb : b < 0) : a + b < 0 :=
  !add.left_id ▸ (add_lt_add_of_le_of_lt Ha Hb)

  theorem add_neg_of_neg_of_neg {a b : A} (Ha : a < 0) (Hb : b < 0) : a + b < 0 :=
  !add.left_id ▸ (add_lt_add_of_lt_of_lt Ha Hb)

  -- TODO: add nonpos version (will be easier with simplifier)
  theorem add_eq_zero_iff_eq_zero_and_eq_zero_of_nonneg_of_noneng {a b : A}
    (Ha : 0 ≤ a) (Hb : 0 ≤ b) : a + b = 0 ↔ a = 0 ∧ b = 0 :=
  iff.intro
    (assume Hab : a + b = 0,
      have Ha' : a ≤ 0, from
        calc
          a = a + 0 : add.right_id
            ... ≤ a + b : add_le_add_left Hb
            ... = 0 : Hab,
      have Haz : a = 0, from le.antisym Ha' Ha,
      have Hb' : b ≤ 0, from
        calc
          b = 0 + b : add.left_id
            ... ≤ a + b : add_le_add_right Ha
            ... = 0 : Hab,
      have Hbz : b = 0, from le.antisym Hb' Hb,
      and.intro Haz Hbz)
    (assume Hab : a = 0 ∧ b = 0,
      (and.elim_left Hab)⁻¹ ▸ (and.elim_right Hab)⁻¹ ▸ (add.right_id 0))

  theorem le_add_of_nonneg_of_le (Ha : 0 ≤ a) (Hbc : b ≤ c) : b ≤ a + c :=
  !add.left_id ▸ add_le_add Ha Hbc

  theorem le_add_of_le_of_nonneg (Hbc : b ≤ c) (Ha : 0 ≤ a) : b ≤ c + a :=
  !add.right_id ▸ add_le_add Hbc Ha

  theorem lt_add_of_pos_of_le (Ha : 0 < a) (Hbc : b ≤ c) : b < a + c :=
  !add.left_id ▸ add_lt_add_of_lt_of_le Ha Hbc

  theorem lt_add_of_le_of_pos (Hbc : b ≤ c) (Ha : 0 < a) : b < c + a :=
  !add.right_id ▸ add_lt_add_of_le_of_lt Hbc Ha

  theorem add_le_of_nonpos_of_le (Ha : a ≤ 0) (Hbc : b ≤ c) : a + b ≤ c :=
  !add.left_id ▸ add_le_add Ha Hbc

  theorem add_le_of_le_of_nonpos (Hbc : b ≤ c) (Ha : a ≤ 0) : b + a ≤ c :=
  !add.right_id ▸ add_le_add Hbc Ha

  theorem add_lt_of_neg_of_le (Ha : a < 0) (Hbc : b ≤ c) : a + b < c :=
  !add.left_id ▸ add_lt_add_of_lt_of_le Ha Hbc

  theorem add_lt_of_le_of_neg (Hbc : b ≤ c) (Ha : a < 0) : b + a < c :=
  !add.right_id ▸ add_lt_add_of_le_of_lt Hbc Ha

  theorem lt_add_of_nonneg_of_lt (Ha : 0 ≤ a) (Hbc : b < c) : b < a + c :=
  !add.left_id ▸ add_lt_add_of_le_of_lt Ha Hbc

  theorem lt_add_of_lt_of_nonneg (Hbc : b < c) (Ha : 0 ≤ a) : b < c + a :=
  !add.right_id ▸ add_lt_add_of_lt_of_le Hbc Ha

  theorem lt_add_of_pos_of_lt (Ha : 0 < a) (Hbc : b < c) : b < a + c :=
  !add.left_id ▸ add_lt_add_of_lt_of_lt Ha Hbc

  theorem lt_add_of_lt_of_pos (Hbc : b < c) (Ha : 0 < a) : b < c + a :=
  !add.right_id ▸ add_lt_add_of_lt_of_lt Hbc Ha

  theorem add_lt_of_nonpos_of_lt (Ha : a ≤ 0) (Hbc : b < c) : a + b < c :=
  !add.left_id ▸ add_lt_add_of_le_of_lt Ha Hbc

  theorem add_lt_of_lt_of_nonpos (Hbc : b < c) (Ha : a ≤ 0)  : b + a < c :=
  !add.right_id ▸ add_lt_add_of_lt_of_le Hbc Ha

  theorem add_lt_of_neg_of_lt (Ha : a < 0) (Hbc : b < c) : a + b < c :=
  !add.left_id ▸ add_lt_add_of_lt_of_lt Ha Hbc

  theorem add_lt_of_lt_of_neg (Hbc : b < c) (Ha : a < 0) : b + a < c :=
  !add.right_id ▸ add_lt_add_of_lt_of_lt Hbc Ha

end

-- TODO: there is more we can do if we have max and min (in order.lean as well)

-- TODO: there is more we can do if we assume a ≤ b ↔ ∃c. a + c = b.
-- This covers the natural numbers,
-- but it is not clear whether it provides any further useful generality.

structure ordered_comm_group [class] (A : Type) extends add_comm_group A, order_pair A :=
(add_le_add_left : ∀a b, le a b → ∀c, le (add c a) (add c b))

definition ordered_comm_group.to_ordered_cancel_comm_monoid [instance] (A : Type)
    [s : ordered_comm_group A] : ordered_cancel_comm_monoid A :=
ordered_cancel_comm_monoid.mk ordered_comm_group.add ordered_comm_group.add_assoc
  (@ordered_comm_group.zero A s) add.left_id add.right_id ordered_comm_group.add_comm
  (@add.left_cancel _ _) (@add.right_cancel _ _)
  has_le.le le.refl (@le.trans _ _) (@le.antisym _ _)
  has_lt.lt (@lt_iff_le_and_ne _ _) ordered_comm_group.add_le_add_left
proof
  take a b c : A,
  assume H : a + b ≤ a + c,
  have H' : -a + (a + b) ≤ -a + (a + c), from ordered_comm_group.add_le_add_left _ _ H _,
  !neg_add_cancel_left ▸ !neg_add_cancel_left ▸ H'
qed

section

  variables [s : ordered_comm_group A] (a b c d e : A)
  include s

  theorem neg_le_neg_of_le {a b : A} (H : a ≤ b) : -b ≤ -a :=
  have H1 : 0 ≤ -a + b, from !add.left_inv ▸ !(add_le_add_left H),
  !add_neg_cancel_right ▸ !add.left_id ▸ add_le_add_right H1 (-b)
--  !add.left_id ▸ !add_neg_cancel_right ▸ add_le_add_right H1 (-b)  -- doesn't work?

  theorem neg_le_neg_iff_le : -a ≤ -b ↔ b ≤ a :=
  iff.intro (take H, neg_neg a ▸ neg_neg b ▸ neg_le_neg_of_le H) neg_le_neg_of_le

  theorem neg_nonpos_iff_nonneg : -a ≤ 0 ↔ 0 ≤ a :=
  neg_zero ▸ neg_le_neg_iff_le a 0

  theorem neg_nonneg_iff_nonpos : 0 ≤ -a ↔ a ≤ 0 :=
  neg_zero ▸ neg_le_neg_iff_le 0 a

  theorem neg_lt_neg_of_lt {a b : A} (H : a < b) : -b < -a :=
  have H1 : 0 < -a + b, from !add.left_inv ▸ !(add_lt_add_left H),
  !add_neg_cancel_right ▸ !add.left_id ▸ add_lt_add_right H1 (-b)

  theorem neg_lt_neg_iff_lt : -a < -b ↔ b < a :=
  iff.intro (take H, neg_neg a ▸ neg_neg b ▸ neg_lt_neg_of_lt H) neg_lt_neg_of_lt

  theorem neg_neg_iff_pos : -a < 0 ↔ 0 < a :=
  neg_zero ▸ neg_lt_neg_iff_lt a 0

  theorem neg_pos_iff_neg : 0 < -a ↔ a < 0 :=
  neg_zero ▸ neg_lt_neg_iff_lt 0 a

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

  theorem add_lt_add_iff_lt_neg_add : a + b < c ↔ b < -a + c :=
  have H: a + b < c ↔ -a + (a + b) < -a + c, from iff.symm (!add_lt_add_left_iff),
  !neg_add_cancel_left ▸ H

  theorem add_lt_add_iff_lt_sub_left : a + b < c ↔ b < c - a :=
  !add.comm ▸ !add_lt_add_iff_lt_neg_add

  theorem add_lt_add_iff_lt_sub_right : a + b < c ↔ a < c - b :=
  have H: a + b < c ↔ a + b - b < c - b, from iff.symm (!add_lt_add_right_iff),
  !add_neg_cancel_right ▸ H

  theorem lt_add_iff_neg_add_lt_add : a < b + c ↔ -b + a < c :=
  have H: a < b + c ↔ -b + a < -b + (b + c), from iff.symm (!add_lt_add_left_iff),
  !neg_add_cancel_left ▸ H

  theorem lt_add_iff_sub_left_lt : a < b + c ↔ a - b < c :=
  !add.comm ▸ !lt_add_iff_neg_add_lt_add

  theorem lt_add_iff_sub_right_lt : a < b + c ↔ a - c < b :=
  have H: a < b + c ↔ a - c < b + c - c, from iff.symm (!add_lt_add_right_iff),
  !add_neg_cancel_right ▸ H

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
  add_le_add_left (neg_le_neg_of_le H) c

  theorem sub_le_sub_right {a b : A} (H : a ≤ b) (c : A) : a - c ≤ b - c := add_le_add_right H (-c)

  theorem sub_le_sub {a b c d : A} (Hab : a ≤ b) (Hcd : c ≤ d) : a - d ≤ b - c :=
  add_le_add Hab (neg_le_neg_of_le Hcd)

  theorem sub_lt_sub_left {a b : A} (H : a < b) (c : A) : c - b < c - a :=
  add_lt_add_left (neg_lt_neg_of_lt H) c

  theorem sub_lt_sub_right {a b : A} (H : a < b) (c : A) : a - c < b - c := add_lt_add_right H (-c)

  theorem sub_lt_sub_of_lt_of_lt {a b c d : A} (Hab : a < b) (Hcd : c < d) : a - d < b - c :=
  add_lt_add_of_lt_of_lt Hab (neg_lt_neg_of_lt Hcd)

  theorem sub_lt_sub_of_le_of_lt {a b c d : A} (Hab : a ≤ b) (Hcd : c < d) : a - d < b - c :=
  add_lt_add_of_le_of_lt Hab (neg_lt_neg_of_lt Hcd)

  theorem sub_lt_sub_of_lt_of_le {a b c d : A} (Hab : a < b) (Hcd : c ≤ d) : a - d < b - c :=
  add_lt_add_of_lt_of_le Hab (neg_le_neg_of_le Hcd)

end

-- TODO: additional facts if the ordering is a linear ordering (e.g. -a = a ↔ a = 0)

-- TODO: structures with abs

end algebra
