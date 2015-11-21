/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

Partially ordered additive groups, modeled on Isabelle's library. We could refine the structures,
but we would have to declare more inheritance paths.
Ported from the standard library
-/

import .order .group
open core

namespace algebra

variable {A : Type}

/- partially ordered monoids, such as the natural numbers -/

structure ordered_cancel_comm_monoid [class] (A : Type) extends add_comm_monoid A,
  add_left_cancel_semigroup A, add_right_cancel_semigroup A, order_pair A :=
(add_le_add_left : Πa b, le a b → Πc, le (add c a) (add c b))
(le_of_add_le_add_left : Πa b c, le (add a b) (add a c) → le b c)

section
  variables [s : ordered_cancel_comm_monoid A]
  variables {a b c d e : A}
  include s

  definition add_le_add_left (H : a ≤ b) (c : A) : c + a ≤ c + b :=
  !ordered_cancel_comm_monoid.add_le_add_left H c

  definition add_le_add_right (H : a ≤ b) (c : A) : a + c ≤ b + c :=
  (add.comm c a) ▸ (add.comm c b) ▸ (add_le_add_left H c)

  definition add_le_add (Hab : a ≤ b) (Hcd : c ≤ d) : a + c ≤ b + d :=
  le.trans (add_le_add_right Hab c) (add_le_add_left Hcd b)

  definition add_lt_add_left (H : a < b) (c : A) : c + a < c + b :=
  have H1 : c + a ≤ c + b, from add_le_add_left (le_of_lt H) c,
  have H2 : c + a ≠ c + b, from
    take H3 : c + a = c + b,
    have H4 : a = b, from add.left_cancel H3,
    ne_of_lt H H4,
  lt_of_le_of_ne H1 H2

  definition add_lt_add_right (H : a < b) (c : A) : a + c < b + c :=
  begin
    rewrite [add.comm, {b + _}add.comm],
    exact (add_lt_add_left H c)
  end

  definition le_add_of_nonneg_right (H : b ≥ 0) : a ≤ a + b :=
  begin
    have H1 : a + b ≥ a + 0, from add_le_add_left H a,
    rewrite add_zero at H1,
    exact H1
  end

  definition le_add_of_nonneg_left (H : b ≥ 0) : a ≤ b + a :=
  begin
    have H1 : 0 + a ≤ b + a, from add_le_add_right H a,
    rewrite zero_add at H1,
    exact H1
  end

  definition add_lt_add (Hab : a < b) (Hcd : c < d) : a + c < b + d :=
  lt.trans (add_lt_add_right Hab c) (add_lt_add_left Hcd b)

  definition add_lt_add_of_le_of_lt (Hab : a ≤ b) (Hcd : c < d) : a + c < b + d :=
  lt_of_le_of_lt (add_le_add_right Hab c) (add_lt_add_left Hcd b)

  definition add_lt_add_of_lt_of_le (Hab : a < b) (Hcd : c ≤ d) : a + c < b + d :=
  lt_of_lt_of_le (add_lt_add_right Hab c) (add_le_add_left Hcd b)

  definition lt_add_of_pos_right (H : b > 0) : a < a + b := !add_zero ▸ add_lt_add_left H a

  definition lt_add_of_pos_left (H : b > 0) : a < b + a := !zero_add ▸ add_lt_add_right H a

  -- here we start using le_of_add_le_add_left.
  definition le_of_add_le_add_left (H : a + b ≤ a + c) : b ≤ c :=
  !ordered_cancel_comm_monoid.le_of_add_le_add_left H

  definition le_of_add_le_add_right (H : a + b ≤ c + b) : a ≤ c :=
  le_of_add_le_add_left (show b + a ≤ b + c, begin rewrite [add.comm, {b + _}add.comm], exact H end)

  definition lt_of_add_lt_add_left (H : a + b < a + c) : b < c :=
  have H1 : b ≤ c, from le_of_add_le_add_left (le_of_lt H),
  have H2 : b ≠ c, from
    assume H3 : b = c, lt.irrefl _ (H3 ▸ H),
  lt_of_le_of_ne H1 H2

  definition lt_of_add_lt_add_right (H : a + b < c + b) : a < c :=
  lt_of_add_lt_add_left ((add.comm a b) ▸ (add.comm c b) ▸ H)

  definition add_le_add_left_iff (a b c : A) : a + b ≤ a + c ↔ b ≤ c :=
  iff.intro le_of_add_le_add_left (assume H, add_le_add_left H _)

  definition add_le_add_right_iff (a b c : A) : a + b ≤ c + b ↔ a ≤ c :=
  iff.intro le_of_add_le_add_right (assume H, add_le_add_right H _)

  definition add_lt_add_left_iff (a b c : A) : a + b < a + c ↔ b < c :=
  iff.intro lt_of_add_lt_add_left (assume H, add_lt_add_left H _)

  definition add_lt_add_right_iff (a b c : A) : a + b < c + b ↔ a < c :=
  iff.intro lt_of_add_lt_add_right (assume H, add_lt_add_right H _)

  -- here we start using properties of zero.
  definition add_nonneg (Ha : 0 ≤ a) (Hb : 0 ≤ b) : 0 ≤ a + b :=
  !zero_add ▸ (add_le_add Ha Hb)

  definition add_pos (Ha : 0 < a) (Hb : 0 < b) : 0 < a + b :=
  !zero_add ▸ (add_lt_add Ha Hb)

  definition add_pos_of_pos_of_nonneg (Ha : 0 < a) (Hb : 0 ≤ b) : 0 < a + b :=
  !zero_add ▸ (add_lt_add_of_lt_of_le Ha Hb)

  definition add_pos_of_nonneg_of_pos (Ha : 0 ≤ a) (Hb : 0 < b) : 0 < a + b :=
  !zero_add ▸ (add_lt_add_of_le_of_lt Ha Hb)

  definition add_nonpos (Ha : a ≤ 0) (Hb : b ≤ 0) : a + b ≤ 0 :=
  !zero_add ▸ (add_le_add Ha Hb)

  definition add_neg (Ha : a < 0) (Hb : b < 0) : a + b < 0 :=
  !zero_add ▸ (add_lt_add Ha Hb)

  definition add_neg_of_neg_of_nonpos (Ha : a < 0) (Hb : b ≤ 0) : a + b < 0 :=
  !zero_add ▸ (add_lt_add_of_lt_of_le Ha Hb)

  definition add_neg_of_nonpos_of_neg (Ha : a ≤ 0) (Hb : b < 0) : a + b < 0 :=
  !zero_add ▸ (add_lt_add_of_le_of_lt Ha Hb)

  -- TODO: add nonpos version (will be easier with simplifier)
  definition add_eq_zero_iff_eq_zero_and_eq_zero_of_nonneg_of_nonneg
    (Ha : 0 ≤ a) (Hb : 0 ≤ b) : a + b = 0 ↔ a = 0 × b = 0 :=
  iff.intro
    (assume Hab : a + b = 0,
      have Ha' : a ≤ 0, from
        calc
          a     = a + 0 : by rewrite add_zero
            ... ≤ a + b : add_le_add_left Hb
            ... = 0     : Hab,
      have Haz : a = 0, from le.antisymm Ha' Ha,
      have Hb' : b ≤ 0, from
        calc
          b     = 0 + b : by rewrite zero_add
            ... ≤ a + b : add_le_add_right Ha
            ... = 0     : Hab,
      have Hbz : b = 0, from le.antisymm Hb' Hb,
      pair Haz Hbz)
    (assume Hab : a = 0 × b = 0,
      match Hab with
      | pair Ha' Hb' := by rewrite [Ha', Hb', add_zero]
      end)

  definition le_add_of_nonneg_of_le (Ha : 0 ≤ a) (Hbc : b ≤ c) : b ≤ a + c :=
  !zero_add ▸ add_le_add Ha Hbc

  definition le_add_of_le_of_nonneg (Hbc : b ≤ c) (Ha : 0 ≤ a) : b ≤ c + a :=
  !add_zero ▸ add_le_add Hbc Ha

  definition lt_add_of_pos_of_le (Ha : 0 < a) (Hbc : b ≤ c) : b < a + c :=
  !zero_add ▸ add_lt_add_of_lt_of_le Ha Hbc

  definition lt_add_of_le_of_pos (Hbc : b ≤ c) (Ha : 0 < a) : b < c + a :=
  !add_zero ▸ add_lt_add_of_le_of_lt Hbc Ha

  definition add_le_of_nonpos_of_le (Ha : a ≤ 0) (Hbc : b ≤ c) : a + b ≤ c :=
  !zero_add ▸ add_le_add Ha Hbc

  definition add_le_of_le_of_nonpos (Hbc : b ≤ c) (Ha : a ≤ 0) : b + a ≤ c :=
  !add_zero ▸ add_le_add Hbc Ha

  definition add_lt_of_neg_of_le (Ha : a < 0) (Hbc : b ≤ c) : a + b < c :=
  !zero_add ▸ add_lt_add_of_lt_of_le Ha Hbc

  definition add_lt_of_le_of_neg (Hbc : b ≤ c) (Ha : a < 0) : b + a < c :=
  !add_zero ▸ add_lt_add_of_le_of_lt Hbc Ha

  definition lt_add_of_nonneg_of_lt (Ha : 0 ≤ a) (Hbc : b < c) : b < a + c :=
  !zero_add ▸ add_lt_add_of_le_of_lt Ha Hbc

  definition lt_add_of_lt_of_nonneg (Hbc : b < c) (Ha : 0 ≤ a) : b < c + a :=
  !add_zero ▸ add_lt_add_of_lt_of_le Hbc Ha

  definition lt_add_of_pos_of_lt (Ha : 0 < a) (Hbc : b < c) : b < a + c :=
  !zero_add ▸ add_lt_add Ha Hbc

  definition lt_add_of_lt_of_pos (Hbc : b < c) (Ha : 0 < a) : b < c + a :=
  !add_zero ▸ add_lt_add Hbc Ha

  definition add_lt_of_nonpos_of_lt (Ha : a ≤ 0) (Hbc : b < c) : a + b < c :=
  !zero_add ▸ add_lt_add_of_le_of_lt Ha Hbc

  definition add_lt_of_lt_of_nonpos (Hbc : b < c) (Ha : a ≤ 0)  : b + a < c :=
  !add_zero ▸ add_lt_add_of_lt_of_le Hbc Ha

  definition add_lt_of_neg_of_lt (Ha : a < 0) (Hbc : b < c) : a + b < c :=
  !zero_add ▸ add_lt_add Ha Hbc

  definition add_lt_of_lt_of_neg (Hbc : b < c) (Ha : a < 0) : b + a < c :=
  !add_zero ▸ add_lt_add Hbc Ha
end

-- TODO: add properties of max and min

/- partially ordered groups -/

structure ordered_comm_group [class] (A : Type) extends add_comm_group A, order_pair A :=
(add_le_add_left : Πa b, le a b → Πc, le (add c a) (add c b))

definition ordered_comm_group.le_of_add_le_add_left [s : ordered_comm_group A] {a b c : A} (H : a + b ≤ a + c) : b ≤ c :=
assert H' : -a + (a + b) ≤ -a + (a + c), from ordered_comm_group.add_le_add_left _ _ H _,
by rewrite *neg_add_cancel_left at H'; exact H'

definition ordered_comm_group.to_ordered_cancel_comm_monoid [instance] [reducible]
    [s : ordered_comm_group A] : ordered_cancel_comm_monoid A :=
⦃ ordered_cancel_comm_monoid, s,
  add_left_cancel       := @add.left_cancel A _,
  add_right_cancel      := @add.right_cancel A _,
  le_of_add_le_add_left := @ordered_comm_group.le_of_add_le_add_left A _ ⦄

section
  variables [s : ordered_comm_group A] (a b c d e : A)
  include s

  definition neg_le_neg {a b : A} (H : a ≤ b) : -b ≤ -a :=
  have H1 : 0 ≤ -a + b, from !add.left_inv ▸ !(add_le_add_left H),
  !add_neg_cancel_right ▸ !zero_add ▸ add_le_add_right H1 (-b)

  definition le_of_neg_le_neg {a b : A} (H : -b ≤ -a) : a ≤ b :=
  neg_neg a ▸ neg_neg b ▸ neg_le_neg H

  definition neg_le_neg_iff_le : -a ≤ -b ↔ b ≤ a :=
  iff.intro le_of_neg_le_neg neg_le_neg

  definition nonneg_of_neg_nonpos {a : A} (H : -a ≤ 0) : 0 ≤ a :=
  le_of_neg_le_neg (neg_zero⁻¹ ▸ H)

  definition neg_nonpos_of_nonneg {a : A} (H : 0 ≤ a) : -a ≤ 0 :=
  neg_zero ▸ neg_le_neg H

  definition neg_nonpos_iff_nonneg : -a ≤ 0 ↔ 0 ≤ a :=
  iff.intro nonneg_of_neg_nonpos neg_nonpos_of_nonneg

  definition nonpos_of_neg_nonneg {a : A} (H : 0 ≤ -a) : a ≤ 0 :=
  le_of_neg_le_neg (neg_zero⁻¹ ▸ H)

  definition neg_nonneg_of_nonpos {a : A} (H : a ≤ 0) : 0 ≤ -a :=
  neg_zero ▸ neg_le_neg H

  definition neg_nonneg_iff_nonpos : 0 ≤ -a ↔ a ≤ 0 :=
  iff.intro nonpos_of_neg_nonneg neg_nonneg_of_nonpos

  definition neg_lt_neg {a b : A} (H : a < b) : -b < -a :=
  have H1 : 0 < -a + b, from !add.left_inv ▸ !(add_lt_add_left H),
  !add_neg_cancel_right ▸ !zero_add ▸ add_lt_add_right H1 (-b)

  definition lt_of_neg_lt_neg {a b : A} (H : -b < -a) : a < b :=
  neg_neg a ▸ neg_neg b ▸ neg_lt_neg H

  definition neg_lt_neg_iff_lt : -a < -b ↔ b < a :=
  iff.intro lt_of_neg_lt_neg neg_lt_neg

  definition pos_of_neg_neg {a : A} (H : -a < 0) : 0 < a :=
  lt_of_neg_lt_neg (neg_zero⁻¹ ▸ H)

  definition neg_neg_of_pos {a : A} (H : 0 < a) : -a < 0 :=
  neg_zero ▸ neg_lt_neg H

  definition neg_neg_iff_pos : -a < 0 ↔ 0 < a :=
  iff.intro pos_of_neg_neg neg_neg_of_pos

  definition neg_of_neg_pos {a : A} (H : 0 < -a) : a < 0 :=
  lt_of_neg_lt_neg (neg_zero⁻¹ ▸ H)

  definition neg_pos_of_neg {a : A} (H : a < 0) : 0 < -a :=
  neg_zero ▸ neg_lt_neg H

  definition neg_pos_iff_neg : 0 < -a ↔ a < 0 :=
  iff.intro neg_of_neg_pos neg_pos_of_neg

  definition le_neg_iff_le_neg : a ≤ -b ↔ b ≤ -a := !neg_neg ▸ !neg_le_neg_iff_le

  definition neg_le_iff_neg_le : -a ≤ b ↔ -b ≤ a := !neg_neg ▸ !neg_le_neg_iff_le

  definition lt_neg_iff_lt_neg : a < -b ↔ b < -a := !neg_neg ▸ !neg_lt_neg_iff_lt

  definition neg_lt_iff_neg_lt : -a < b ↔ -b < a := !neg_neg ▸ !neg_lt_neg_iff_lt

  definition sub_nonneg_iff_le : 0 ≤ a - b ↔ b ≤ a := !sub_self ▸ !add_le_add_right_iff

  definition sub_nonpos_iff_le : a - b ≤ 0 ↔ a ≤ b := !sub_self ▸ !add_le_add_right_iff

  definition sub_pos_iff_lt : 0 < a - b ↔ b < a := !sub_self ▸ !add_lt_add_right_iff

  definition sub_neg_iff_lt : a - b < 0 ↔ a < b := !sub_self ▸ !add_lt_add_right_iff

  definition add_le_iff_le_neg_add : a + b ≤ c ↔ b ≤ -a + c :=
  have H: a + b ≤ c ↔ -a + (a + b) ≤ -a + c, from iff.symm (!add_le_add_left_iff),
  !neg_add_cancel_left ▸ H

  definition add_le_iff_le_sub_left : a + b ≤ c ↔ b ≤ c - a :=
  by rewrite [sub_eq_add_neg, {c+_}add.comm]; apply add_le_iff_le_neg_add

  definition add_le_iff_le_sub_right : a + b ≤ c ↔ a ≤ c - b :=
  have H: a + b ≤ c ↔ a + b - b ≤ c - b, from iff.symm (!add_le_add_right_iff),
  !add_neg_cancel_right ▸ H

  definition le_add_iff_neg_add_le : a ≤ b + c ↔ -b + a ≤ c :=
  assert H: a ≤ b + c ↔ -b + a ≤ -b + (b + c), from iff.symm (!add_le_add_left_iff),
  by rewrite neg_add_cancel_left at H; exact H

  definition le_add_iff_sub_left_le : a ≤ b + c ↔ a - b ≤ c :=
  by rewrite [sub_eq_add_neg, {a+_}add.comm]; apply le_add_iff_neg_add_le

  definition le_add_iff_sub_right_le : a ≤ b + c ↔ a - c ≤ b :=
  assert H: a ≤ b + c ↔ a - c ≤ b + c - c, from iff.symm (!add_le_add_right_iff),
  by rewrite add_neg_cancel_right at H; exact H

  definition add_lt_iff_lt_neg_add_left : a + b < c ↔ b < -a + c :=
  assert H: a + b < c ↔ -a + (a + b) < -a + c, from iff.symm (!add_lt_add_left_iff),
  begin rewrite neg_add_cancel_left at H, exact H end

  definition add_lt_iff_lt_neg_add_right : a + b < c ↔ a < -b + c :=
  by rewrite add.comm; apply add_lt_iff_lt_neg_add_left

  definition add_lt_iff_lt_sub_left : a + b < c ↔ b < c - a :=
  begin
    rewrite [sub_eq_add_neg, {c+_}add.comm],
    apply add_lt_iff_lt_neg_add_left
  end

  definition add_lt_add_iff_lt_sub_right : a + b < c ↔ a < c - b :=
  assert H: a + b < c ↔ a + b - b < c - b, from iff.symm (!add_lt_add_right_iff),
  by rewrite add_neg_cancel_right at H; exact H

  definition lt_add_iff_neg_add_lt_left : a < b + c ↔ -b + a < c :=
  assert H: a < b + c ↔ -b + a < -b + (b + c), from iff.symm (!add_lt_add_left_iff),
  by rewrite neg_add_cancel_left at H; exact H

  definition lt_add_iff_neg_add_lt_right : a < b + c ↔ -c + a < b :=
  by rewrite add.comm; apply lt_add_iff_neg_add_lt_left

  definition lt_add_iff_sub_lt_left : a < b + c ↔ a - b < c :=
  by rewrite [sub_eq_add_neg, {a + _}add.comm]; apply lt_add_iff_neg_add_lt_left

  definition lt_add_iff_sub_lt_right : a < b + c ↔ a - c < b :=
  by rewrite add.comm; apply lt_add_iff_sub_lt_left

  -- TODO: the Isabelle library has varations on a + b ≤ b ↔ a ≤ 0
  definition le_iff_le_of_sub_eq_sub {a b c d : A} (H : a - b = c - d) : a ≤ b ↔ c ≤ d :=
  calc
    a ≤ b ↔ a - b ≤ 0   : iff.symm (sub_nonpos_iff_le a b)
      ... = (c - d ≤ 0) : by rewrite H
      ... ↔ c ≤ d       : sub_nonpos_iff_le c d

  definition lt_iff_lt_of_sub_eq_sub {a b c d : A} (H : a - b = c - d) : a < b ↔ c < d :=
  calc
    a < b ↔ a - b < 0   : iff.symm (sub_neg_iff_lt a b)
      ... = (c - d < 0) : by rewrite H
      ... ↔ c < d       : sub_neg_iff_lt c d

  definition sub_le_sub_left {a b : A} (H : a ≤ b) (c : A) : c - b ≤ c - a :=
  add_le_add_left (neg_le_neg H) c

  definition sub_le_sub_right {a b : A} (H : a ≤ b) (c : A) : a - c ≤ b - c := add_le_add_right H (-c)

  definition sub_le_sub {a b c d : A} (Hab : a ≤ b) (Hcd : c ≤ d) : a - d ≤ b - c :=
  add_le_add Hab (neg_le_neg Hcd)

  definition sub_lt_sub_left {a b : A} (H : a < b) (c : A) : c - b < c - a :=
  add_lt_add_left (neg_lt_neg H) c

  definition sub_lt_sub_right {a b : A} (H : a < b) (c : A) : a - c < b - c := add_lt_add_right H (-c)

  definition sub_lt_sub {a b c d : A} (Hab : a < b) (Hcd : c < d) : a - d < b - c :=
  add_lt_add Hab (neg_lt_neg Hcd)

  definition sub_lt_sub_of_le_of_lt {a b c d : A} (Hab : a ≤ b) (Hcd : c < d) : a - d < b - c :=
  add_lt_add_of_le_of_lt Hab (neg_lt_neg Hcd)

  definition sub_lt_sub_of_lt_of_le {a b c d : A} (Hab : a < b) (Hcd : c ≤ d) : a - d < b - c :=
  add_lt_add_of_lt_of_le Hab (neg_le_neg Hcd)

  definition sub_le_self (a : A) {b : A} (H : b ≥ 0) : a - b ≤ a :=
  calc
    a - b = a + -b : rfl
      ... ≤ a + 0  : add_le_add_left (neg_nonpos_of_nonneg H)
      ... = a      : by rewrite add_zero

  definition sub_lt_self (a : A) {b : A} (H : b > 0) : a - b < a :=
  calc
    a - b = a + -b : rfl
      ... < a + 0  : add_lt_add_left (neg_neg_of_pos H)
      ... = a      : by rewrite add_zero
end

structure decidable_linear_ordered_comm_group [class] (A : Type)
    extends ordered_comm_group A, decidable_linear_order A

section
  variables [s : decidable_linear_ordered_comm_group A]
  variables {a b c d e : A}
  include s

  definition eq_zero_of_neg_eq (H : -a = a) : a = 0 :=
  lt.by_cases
    (assume H1 : a < 0,
      have H2: a > 0, from H ▸ neg_pos_of_neg H1,
      absurd H1 (lt.asymm H2))
    (assume H1 : a = 0, H1)
    (assume H1 : a > 0,
      have H2: a < 0, from H ▸ neg_neg_of_pos H1,
      absurd H1 (lt.asymm H2))

  definition abs (a : A) : A := if 0 ≤ a then a else -a

  definition abs_of_nonneg (H : a ≥ 0) : abs a = a := if_pos H

  definition abs_of_pos (H : a > 0) : abs a = a := if_pos (le_of_lt H)

  definition abs_of_neg (H : a < 0) : abs a = -a := if_neg (not_le_of_lt H)

  definition abs_zero : abs 0 = (0:A) := abs_of_nonneg (le.refl _)

  definition abs_of_nonpos (H : a ≤ 0) : abs a = -a :=
  decidable.by_cases
    (assume H1 : a = 0, by rewrite [H1, abs_zero, neg_zero])
    (assume H1 : a ≠ 0,
      have H2 : a < 0, from lt_of_le_of_ne H H1,
      abs_of_neg H2)

  definition abs_neg (a : A) : abs (-a) = abs a :=
  sum.rec_on (le.total 0 a)
    (assume H1 : 0 ≤ a, by rewrite [abs_of_nonpos (neg_nonpos_of_nonneg H1), neg_neg, abs_of_nonneg H1])
    (assume H1 : a ≤ 0, by rewrite [abs_of_nonneg (neg_nonneg_of_nonpos H1), abs_of_nonpos H1])

  definition abs_nonneg (a : A) : abs a ≥ 0 :=
  sum.rec_on (le.total 0 a)
    (assume H : 0 ≤ a, by rewrite (abs_of_nonneg H); exact H)
    (assume H : a ≤ 0,
      calc
          0 ≤ -a    : neg_nonneg_of_nonpos H
        ... = abs a : abs_of_nonpos H)

  definition abs_abs (a : A) : abs (abs a) = abs a := abs_of_nonneg !abs_nonneg

  definition le_abs_self (a : A) : a ≤ abs a :=
  sum.rec_on (le.total 0 a)
    (assume H : 0 ≤ a, abs_of_nonneg H ▸ !le.refl)
    (assume H : a ≤ 0, le.trans H !abs_nonneg)

  definition neg_le_abs_self (a : A) : -a ≤ abs a :=
  !abs_neg ▸ !le_abs_self

  definition eq_zero_of_abs_eq_zero (H : abs a = 0) : a = 0 :=
  have H1 : a ≤ 0, from H ▸ le_abs_self a,
  have H2 : -a ≤ 0, from H ▸ abs_neg a ▸ le_abs_self (-a),
  le.antisymm H1 (nonneg_of_neg_nonpos H2)

  definition abs_eq_zero_iff_eq_zero (a : A) : abs a = 0 ↔ a = 0 :=
  iff.intro eq_zero_of_abs_eq_zero (assume H, ap abs H ⬝ !abs_zero)

  definition abs_pos_of_pos (H : a > 0) : abs a > 0 :=
  by rewrite (abs_of_pos H); exact H

  definition abs_pos_of_neg (H : a < 0) : abs a > 0 :=
  !abs_neg ▸ abs_pos_of_pos (neg_pos_of_neg H)

  definition abs_pos_of_ne_zero (H : a ≠ 0) : abs a > 0 :=
  sum.rec_on (lt_or_gt_of_ne H) abs_pos_of_neg abs_pos_of_pos

  definition abs_sub (a b : A) : abs (a - b) = abs (b - a) :=
  by rewrite [-neg_sub, abs_neg]

  definition abs.by_cases {P : A → Type} {a : A} (H1 : P a) (H2 : P (-a)) : P (abs a) :=
  sum.rec_on (le.total 0 a)
    (assume H : 0 ≤ a, (abs_of_nonneg H)⁻¹ ▸ H1)
    (assume H : a ≤ 0, (abs_of_nonpos H)⁻¹ ▸ H2)

  definition abs_le_of_le_of_neg_le (H1 : a ≤ b) (H2 : -a ≤ b) : abs a ≤ b :=
  abs.by_cases H1 H2

  definition abs_lt_of_lt_of_neg_lt (H1 : a < b) (H2 : -a < b) : abs a < b :=
  abs.by_cases H1 H2

  -- the triangle inequality
  section
    private lemma aux1 {a b : A} (H1 : a + b ≥ 0) (H2 : a ≥ 0) : abs (a + b) ≤ abs a + abs b :=
    decidable.by_cases
      (assume H3 : b ≥ 0,
          calc
            abs (a + b) ≤ abs (a + b)   : le.refl
                ... = a + b             : by rewrite (abs_of_nonneg H1)
                ... = abs a + b         : by rewrite (abs_of_nonneg H2)
                ... = abs a + abs b     : by rewrite (abs_of_nonneg H3))
      (assume H3 : ¬ b ≥ 0,
        assert H4 : b ≤ 0, from le_of_lt (lt_of_not_le H3),
        calc
          abs (a + b) = a + b     : by rewrite (abs_of_nonneg H1)
              ... = abs a + b     : by rewrite (abs_of_nonneg H2)
              ... ≤ abs a + 0     : add_le_add_left H4
              ... ≤ abs a + -b    : add_le_add_left (neg_nonneg_of_nonpos H4)
              ... = abs a + abs b : by rewrite (abs_of_nonpos H4))

    private lemma aux2 {a b : A} (H1 : a + b ≥ 0) : abs (a + b) ≤ abs a + abs b :=
    sum.rec_on (le.total b 0)
      (assume H2 : b ≤ 0,
        have H3 : ¬ a < 0, from
          assume H4 : a < 0,
          have H5 : a + b < 0, from !add_zero ▸ add_lt_add_of_lt_of_le H4 H2,
          not_lt_of_le H1 H5,
        aux1 H1 (le_of_not_lt H3))
      (assume H2 : 0 ≤ b,
        begin
          have H3 : abs (b + a) ≤ abs b + abs a,
          begin
            rewrite add.comm at H1,
            exact aux1 H1 H2
          end,
          rewrite [add.comm, {abs a + _}add.comm],
          exact H3
        end)

    definition abs_add_le_abs_add_abs (a b : A) : abs (a + b) ≤ abs a + abs b :=
    sum.rec_on (le.total 0 (a + b))
      (assume H2 : 0 ≤ a + b, aux2 H2)
      (assume H2 : a + b ≤ 0,
        assert H3 : -a + -b = -(a + b), by rewrite neg_add,
        assert H4 : -(a + b) ≥ 0, from iff.mpr (neg_nonneg_iff_nonpos (a+b)) H2,
        have H5   : -a + -b ≥ 0, begin rewrite -H3 at H4, exact H4 end,
        calc
          abs (a + b) = abs (-a + -b)   : by rewrite [-abs_neg, neg_add]
              ... ≤ abs (-a) + abs (-b) : aux2 H5
              ... = abs a + abs b       : by rewrite *abs_neg)
  end

  definition abs_sub_abs_le_abs_sub (a b : A) : abs a - abs b ≤ abs (a - b) :=
  have H1 : abs a - abs b + abs b ≤ abs (a - b) + abs b, from
    calc
      abs a - abs b + abs b = abs a : by rewrite sub_add_cancel
        ... = abs (a - b + b)       : by rewrite sub_add_cancel
        ... ≤ abs (a - b) + abs b   : abs_add_le_abs_add_abs,
  algebra.le_of_add_le_add_right H1
end

end algebra
