/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: algebra.ordered_group
Authors: Jeremy Avigad

Partially ordered additive groups. Modeled on Isabelle's library. The comments below indicate that
we could refine the structures, though we would have to declare more inheritance paths.
-/

import logic.eq logic.connectives
import data.unit data.sigma data.prod
import algebra.function algebra.binary
import algebra.group algebra.order

open eq eq.ops   -- note: ⁻¹ will be overloaded

namespace algebra

variable {A : Type}

structure ordered_cancel_comm_monoid [class] (A : Type) extends add_comm_monoid A,
add_left_cancel_semigroup A, add_right_cancel_semigroup A, order_pair A :=
(add_le_left : ∀a b c, le a b → le (add c a) (add c b))
(add_le_left_cancel : ∀a b c, le (add c a) (add c b) → le a b)

section

  variables [s : ordered_cancel_comm_monoid A] (a b c d e : A)
  include s

  theorem add_le_left {a b : A} (H : a ≤ b) (c : A) : c + a ≤ c + b :=
  !ordered_cancel_comm_monoid.add_le_left H

  theorem add_le_right {a b : A} (H : a ≤ b) (c : A) : a + c ≤ b + c :=
  (add_comm c a) ▸ (add_comm c b) ▸ (add_le_left H c)

  theorem add_le {a b c d : A} (Hab : a ≤ b) (Hcd : c ≤ d) : a + c ≤ b + d :=
  le_trans (add_le_right Hab c) (add_le_left Hcd b)

  theorem add_lt_left {a b : A} (H : a < b) (c : A) : c + a < c + b :=
  have H1 : c + a ≤ c + b, from add_le_left (lt_imp_le H) c,
  have H2 : c + a ≠ c + b, from
    take H3 : c + a = c + b,
    have H4 : a = b, from add_left_cancel H3,
    lt_imp_ne H H4,
  le_ne_imp_lt H1 H2

  theorem add_lt_right {a b : A} (H : a < b) (c : A) : a + c < b + c :=
  (add_comm c a) ▸ (add_comm c b) ▸ (add_lt_left H c)

  theorem add_lt {a b c d : A} (Hab : a < b) (Hcd : c < d) : a + c < b + d :=
  lt_trans (add_lt_right Hab c) (add_lt_left Hcd b)

  theorem add_le_lt {a b c d : A} (Hab : a ≤ b) (Hcd : c < d) : a + c < b + d :=
  le_lt_trans (add_le_right Hab c) (add_lt_left Hcd b)

  theorem add_lt_le {a b c d : A} (Hab : a < b) (Hcd : c ≤ d) : a + c < b + d :=
  lt_le_trans (add_lt_right Hab c) (add_le_left Hcd b)

  -- here we start using add_le_left_cancel.
  theorem add_le_left_cancel {a b c : A} (H : a + b ≤ a + c) : b ≤ c :=
  !ordered_cancel_comm_monoid.add_le_left_cancel H

  theorem add_le_right_cancel {a b c : A} (H : a + b ≤ c + b) : a ≤ c :=
  add_le_left_cancel ((add_comm a b) ▸ (add_comm c b) ▸ H)

  theorem add_lt_left_cancel {a b c : A} (H : a + b < a + c) : b < c :=
  have H1 : b ≤ c, from add_le_left_cancel (lt_imp_le H),
  have H2 : b ≠ c, from
    assume H3 : b = c, lt_irrefl _ (H3 ▸ H),
  le_ne_imp_lt H1 H2

  theorem add_lt_right_cancel {a b c : A} (H : a + b < c + b) : a < c :=
  add_lt_left_cancel ((add_comm a b) ▸ (add_comm c b) ▸ H)

  theorem add_le_left_iff : a + b ≤ a + c ↔ b ≤ c :=
  iff.intro add_le_left_cancel (assume H, add_le_left H _)

  theorem add_le_right_iff : a + b ≤ c + b ↔ a ≤ c :=
  iff.intro add_le_right_cancel (assume H, add_le_right H _)

  theorem add_lt_left_iff : a + b < a + c ↔ b < c :=
  iff.intro add_lt_left_cancel (assume H, add_lt_left H _)

  theorem add_lt_right_iff : a + b < c + b ↔ a < c :=
  iff.intro add_lt_right_cancel (assume H, add_lt_right H _)

  -- here we start using properties of zero.
  theorem add_nonneg_nonneg {a b : A} (Ha : 0 ≤ a) (Hb : 0 ≤ b) : 0 ≤ a + b :=
  !add_left_id ▸ (add_le Ha Hb)

  theorem add_pos_nonneg {a b : A} (Ha : 0 < a) (Hb : 0 ≤ b) : 0 < a + b :=
  !add_left_id ▸ (add_lt_le Ha Hb)

  theorem add_nonneg_pos {a b : A} (Ha : 0 ≤ a) (Hb : 0 < b) : 0 < a + b :=
  !add_left_id ▸ (add_le_lt Ha Hb)

  theorem add_pos_pos {a b : A} (Ha : 0 < a) (Hb : 0 < b) : 0 < a + b :=
  !add_left_id ▸ (add_lt Ha Hb)

  theorem add_nonpos_nonpos {a b : A} (Ha : a ≤ 0) (Hb : b ≤ 0) : a + b ≤ 0 :=
  !add_left_id ▸ (add_le Ha Hb)
  calc_trans le_eq_trans

  theorem add_neg_nonpos {a b : A} (Ha : a < 0) (Hb : b ≤ 0) : a + b < 0 :=
  !add_left_id ▸ (add_lt_le Ha Hb)

  theorem add_nonpos_neg {a b : A} (Ha : a ≤ 0) (Hb : b < 0) : a + b < 0 :=
  !add_left_id ▸ (add_le_lt Ha Hb)

  theorem add_neg_neg {a b : A} (Ha : a < 0) (Hb : b < 0) : a + b < 0 :=
  !add_left_id ▸ (add_lt Ha Hb)

  -- TODO: add nonpos version (will be easier with simplifier)
  theorem add_nonneg_eq_zero_iff {a b : A} (Ha : 0 ≤ a) (Hb : 0 ≤ b) : a + b = 0 ↔ a = 0 ∧ b = 0 :=
  iff.intro
    (assume Hab : a + b = 0,
      have Ha' : a ≤ 0, from
        calc
          a = a + 0 : add_right_id
            ... ≤ a + b : add_le_left Hb
            ... = 0 : Hab,
      have Haz : a = 0, from le_antisym Ha' Ha,
      have Hb' : b ≤ 0, from
        calc
          b = 0 + b : add_left_id
            ... ≤ a + b : add_le_right Ha
            ... = 0 : Hab,
      have Hbz : b = 0, from le_antisym Hb' Hb,
      and.intro Haz Hbz)
    (assume Hab : a = 0 ∧ b = 0,
      (and.elim_left Hab)⁻¹ ▸ (and.elim_right Hab)⁻¹ ▸ (add_right_id 0))

  theorem le_add_nonneg (Ha : 0 ≤ a) (Hbc : b ≤ c) : b ≤ a + c := !add_left_id ▸ add_le Ha Hbc
  theorem le_nonneg_add (Ha : 0 ≤ a) (Hbc : b ≤ c) : b ≤ c + a := !add_right_id ▸ add_le Hbc Ha
  theorem le_add_pos (Ha : 0 < a) (Hbc : b ≤ c) : b < a + c := !add_left_id ▸ add_lt_le Ha Hbc
  theorem le_pos_add (Ha : 0 < a) (Hbc : b ≤ c) : b < c + a := !add_right_id ▸ add_le_lt Hbc Ha
  theorem le_add_nonpos (Ha : a ≤ 0) (Hbc : b ≤ c) : a + b ≤ c := !add_left_id ▸ add_le Ha Hbc
  theorem le_nonpos_add (Ha : a ≤ 0) (Hbc : b ≤ c) : b + a ≤ c := !add_right_id ▸ add_le Hbc Ha
  theorem le_add_neg (Ha : a < 0) (Hbc : b ≤ c) : a + b < c := !add_left_id ▸ add_lt_le Ha Hbc
  theorem le_neg_add (Ha : a < 0) (Hbc : b ≤ c) : b + a < c := !add_right_id ▸ add_le_lt Hbc Ha
  theorem lt_add_nonneg (Ha : 0 ≤ a) (Hbc : b < c) : b < a + c := !add_left_id ▸ add_le_lt Ha Hbc
  theorem lt_nonneg_add (Ha : 0 ≤ a) (Hbc : b < c) : b < c + a := !add_right_id ▸ add_lt_le Hbc Ha
  theorem lt_add_pos (Ha : 0 < a) (Hbc : b < c) : b < a + c := !add_left_id ▸ add_lt Ha Hbc
  theorem lt_pos_add (Ha : 0 < a) (Hbc : b < c) : b < c + a := !add_right_id ▸ add_lt Hbc Ha
  theorem lt_add_nonpos (Ha : a ≤ 0) (Hbc : b < c) : a + b < c := !add_left_id ▸ add_le_lt Ha Hbc
  theorem lt_nonpos_add (Ha : a ≤ 0) (Hbc : b < c) : b + a < c := !add_right_id ▸ add_lt_le Hbc Ha
  theorem lt_add_neg (Ha : a < 0) (Hbc : b < c) : a + b < c := !add_left_id ▸ add_lt Ha Hbc
  theorem lt_neg_add (Ha : a < 0) (Hbc : b < c) : b + a < c := !add_right_id ▸ add_lt Hbc Ha
end

-- TODO: there is more we can do if we have max and min (in order.lean as well)

-- TODO: there is more we can do if we assume a ≤ b ↔ ∃c. a + c = b, but it is not clear whether
-- this gives us any useful generality

structure ordered_comm_group [class] (A : Type) extends add_comm_group A, order_pair A :=
(add_le_left : ∀a b c, le a b → le (add c a) (add c b))

definition ordered_comm_group.to_ordered_cancel_comm_monoid [instance] (A : Type)
    [s : ordered_comm_group A] : ordered_cancel_comm_monoid A :=
ordered_cancel_comm_monoid.mk has_add.add add_assoc has_zero.zero add_left_id add_right_id add_comm
(@add_left_cancel _ _) (@add_right_cancel _ _) has_le.le le_refl (@le_trans _ _) (@le_antisym _ _)
has_lt.lt (@lt_iff_le_ne _ _) ordered_comm_group.add_le_left
proof
  take a b c : A,
  assume H : c + a ≤ c + b,
  have H' : -c + (c + a) ≤ -c + (c + b), from ordered_comm_group.add_le_left _ _ _ H,
  !neg_add_cancel_left ▸ !neg_add_cancel_left ▸ H'
qed

end algebra
