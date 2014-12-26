/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: data.int.order
Authors: Floris van Doorn, Jeremy Avigad

The order relation on the integers. We show that int is an instance of linear_comm_ordered_ring
and transfer the results.
-/

import .basic algebra.ordered_ring

open nat
open decidable
open fake_simplifier
open int eq.ops

namespace int

private definition nonneg (a : ℤ) : Prop := cases_on a (take n, true) (take n, false)
definition le (a b : ℤ) : Prop := nonneg (sub b a)
definition lt (a b : ℤ) : Prop := le (add a 1) b

infix - := int.sub
infix <= := int.le
infix ≤  := int.le
infix <  := int.lt

private definition decidable_nonneg [instance] (a : ℤ) : decidable (nonneg a) := cases_on a _ _
definition decidable_le [instance] (a b : ℤ) : decidable (a ≤ b) := decidable_nonneg _
definition decidable_lt [instance] (a b : ℤ) : decidable (a < b) := decidable_nonneg _

private theorem nonneg.elim {a : ℤ} : nonneg a → ∃n : ℕ, a = n :=
cases_on a (take n H, exists.intro n rfl) (take n' H, false.elim H)

private theorem nonneg_or_nonneg_neg (a : ℤ) : nonneg a ∨ nonneg (-a) :=
cases_on a (take n, or.inl trivial) (take n, or.inr trivial)

theorem le.intro {a b : ℤ} {n : ℕ} (H : a + n = b) : a ≤ b :=
have H1 : b - a = n, from (eq_add_neg_of_add_eq (!add.comm ▸ H))⁻¹,
have H2 : nonneg n, from true.intro,
show nonneg (b - a), from H1⁻¹ ▸ H2

theorem le.elim {a b : ℤ} (H : a ≤ b) : ∃n : ℕ, a + n = b :=
obtain (n : ℕ) (H1 : b - a = n), from nonneg.elim H,
exists.intro n (!add.comm ▸ iff.mp' !add_eq_iff_eq_add_neg (H1⁻¹))

theorem le.total (a b : ℤ) : a ≤ b ∨ b ≤ a :=
or.elim (nonneg_or_nonneg_neg (b - a))
  (assume H, or.inl H)
  (assume H : nonneg (-(b - a)),
    have H0 : -(b - a) = a - b, from neg_sub_eq b a,
    have H1 : nonneg (a - b), from H0 ▸ H,    -- too bad: can't do it in one step
    or.inr H1)

theorem of_nat_le_of_nat (n m : ℕ) : of_nat n ≤ of_nat m ↔ n ≤ m :=
iff.intro
  (assume H : of_nat n ≤ of_nat m,
    obtain (k : ℕ) (Hk : of_nat n + of_nat k = of_nat m), from le.elim H,
    have H2 : n + k = m, from of_nat_inj ((add_of_nat n k)⁻¹ ⬝ Hk),
    nat.le_intro H2)
  (assume H : n ≤ m,
    obtain (k : ℕ) (Hk : n + k = m), from nat.le_elim H,
    have H2 : of_nat n + of_nat k = of_nat m, from Hk ▸ add_of_nat n k,
    le.intro H2)

theorem lt_add_succ (a : ℤ) (n : ℕ) : a < a + succ n :=
le.intro (show a + 1 + n = a + succ n, from
  calc
    a + 1 + n = a + (1 + n) : add.assoc
      ... = a + (n + 1)     : add.comm
      ... = a + succ n      : rfl)

theorem lt.intro {a b : ℤ} {n : ℕ} (H : a + succ n = b) : a < b :=
H ▸ lt_add_succ a n

theorem lt.elim {a b : ℤ} (H : a < b) : ∃n : ℕ, a + succ n = b :=
obtain (n : ℕ) (Hn : a + 1 + n = b), from le.elim H,
have H2 : a + succ n = b, from
  calc
    a + succ n = a + 1 + n : by simp
      ... = b : Hn,
exists.intro n H2

theorem of_nat_lt_of_nat (n m : ℕ) : of_nat n < of_nat m ↔ n < m :=
calc
  of_nat n < of_nat m ↔ of_nat n + 1 ≤ of_nat m : iff.refl
    ... ↔ of_nat (succ n) ≤ of_nat m            : of_nat_succ n ▸ !iff.refl
    ... ↔ succ n ≤ m                            : of_nat_le_of_nat
    ... ↔ n < m                                 : iff.symm (lt_iff_succ_le _ _)

/- show that the integers form an ordered additive group -/

theorem le.refl (a : ℤ) : a ≤ a :=
le.intro (add_zero a)

theorem le.trans {a b c : ℤ} (H1 : a ≤ b) (H2 : b ≤ c) : a ≤ c :=
obtain (n : ℕ) (Hn : a + n = b), from le.elim H1,
obtain (m : ℕ) (Hm : b + m = c), from le.elim H2,
have H3 : a + of_nat (n + m) = c, from
  calc
    a + of_nat (n + m) = a + (of_nat n + m) : {(add_of_nat n m)⁻¹}
      ... = a + n + m : (add.assoc a n m)⁻¹
      ... = b + m : {Hn}
      ... = c : Hm,
le.intro H3

theorem le.antisymm {a b : ℤ} (H1 : a ≤ b) (H2 : b ≤ a) : a = b :=
obtain (n : ℕ) (Hn : a + n = b), from le.elim H1,
obtain (m : ℕ) (Hm : b + m = a), from le.elim H2,
have H3 : a + of_nat (n + m) = a + 0, from
  calc
    a + of_nat (n + m) = a + (of_nat n + m) : {(add_of_nat n m)⁻¹}
      ... = a + n + m : (add.assoc a n m)⁻¹
      ... = b + m : {Hn}
      ... = a : Hm
      ... = a + 0 : (add_zero a)⁻¹,
have H4 : of_nat (n + m) = of_nat 0, from add.left_cancel H3,
have H5 : n + m = 0, from of_nat_inj H4,
have H6 : n = 0, from nat.eq_zero_of_add_eq_zero_right H5,
show a = b, from
  calc
    a = a + of_nat 0 : (add_zero a)⁻¹
      ... = a + n : {H6⁻¹}
      ... = b : Hn

theorem lt.irrefl (a : ℤ) : ¬ a < a :=
(assume H : a < a,
  obtain (n : ℕ) (Hn : a + succ n = a), from lt.elim H,
  have H2 : a + succ n = a + 0, from
    calc
      a + succ n = a : Hn
        ... = a + 0 : by simp,
  have H3 : succ n = 0, from add.left_cancel H2,
  have H4 : succ n = 0, from of_nat_inj H3,
  absurd H4 !succ_ne_zero)

theorem ne_of_lt {a b : ℤ} (H : a < b) : a ≠ b :=
(assume H2 : a = b, absurd (H2 ▸ H) (lt.irrefl b))

theorem succ_le_of_lt {a b : ℤ} (H : a < b) : a + 1 ≤ b := H

theorem lt_of_le_succ {a b : ℤ} (H : a + 1 ≤ b) : a < b := H

theorem le_of_lt {a b : ℤ} (H : a < b) : a ≤ b :=
obtain (n : ℕ) (Hn : a + succ n = b), from lt.elim H,
le.intro Hn

theorem lt_iff_le_and_ne (a b : ℤ) : a < b ↔ (a ≤ b ∧ a ≠ b) :=
iff.intro
  (assume H, and.intro (le_of_lt H) (ne_of_lt H))
  (assume H,
    have H1 : a ≤ b, from and.elim_left H,
    have H2 : a ≠ b, from and.elim_right H,
    obtain (n : ℕ) (Hn : a + n = b), from le.elim H1,
    have H3 : n ≠ 0, from (assume H' : n = 0, H2 (!add_zero ▸ H' ▸ Hn)),
    obtain (k : ℕ) (Hk : n = succ k), from nat.exists_eq_succ_of_ne_zero H3,
    lt.intro (Hk ▸ Hn))

theorem le_iff_lt_or_eq (a b : ℤ) : a ≤ b ↔ (a < b ∨ a = b) :=
iff.intro
  (assume H,
    by_cases
      (assume H1 : a = b, or.inr H1)
      (assume H1 : a ≠ b,
        obtain (n : ℕ) (Hn : a + n = b), from le.elim H,
        have H2 : n ≠ 0, from (assume H' : n = 0, H1 (!add_zero ▸ H' ▸ Hn)),
        obtain (k : ℕ) (Hk : n = succ k), from nat.exists_eq_succ_of_ne_zero H2,
        or.inl (lt.intro (Hk ▸ Hn))))
  (assume H,
    or.elim H
      (assume H1, le_of_lt H1)
      (assume H1, H1 ▸ !le.refl))

theorem lt_succ (a : ℤ) : a < a + 1 :=
le.refl (a + 1)

theorem add_le_add_left {a b : ℤ} (H : a ≤ b) (c : ℤ) : c + a ≤ c + b :=
obtain (n : ℕ) (Hn : a + n = b), from le.elim H,
have H2 : c + a + n = c + b, from
  calc
    c + a + n = c + (a + n) : add.assoc c a n
      ... = c + b : {Hn},
le.intro H2

theorem mul_nonneg {a b : ℤ} (Ha : 0 ≤ a) (Hb : 0 ≤ b) : 0 ≤ a * b :=
obtain (n : ℕ) (Hn : 0 + n = a), from le.elim Ha,
obtain (m : ℕ) (Hm : 0 + m = b), from le.elim Hb,
le.intro
  (eq.symm
    (calc
      a * b = (0 + n) * b : Hn
        ... = n * b       : zero_add
        ... = n * (0 + m) : Hm
        ... = n * m       : zero_add
        ... = 0 + n * m   : zero_add))

theorem mul_pos {a b : ℤ} (Ha : 0 < a) (Hb : 0 < b) : 0 < a * b :=
obtain (n : ℕ) (Hn : 0 + succ n = a), from lt.elim Ha,
obtain (m : ℕ) (Hm : 0 + succ m = b), from lt.elim Hb,
lt.intro
  (eq.symm
    (calc
      a * b = (0 + succ n) * b                 : Hn
        ... = succ n * b                       : zero_add
        ... = succ n * (0 + succ m)            : Hm
        ... = succ n * succ m                  : zero_add
        ... = of_nat (succ n * succ m)         : mul_of_nat
        ... = of_nat (succ n * m + succ n)     : nat.mul_succ
        ... = of_nat (succ (succ n * m + n))   : nat.add_succ
        ... = 0 + succ (succ n * m + n)        : zero_add))

protected definition linear_ordered_comm_ring : algebra.linear_ordered_comm_ring int :=
algebra.linear_ordered_comm_ring.mk add add.assoc zero zero_add add_zero neg add.left_inv
  add.comm mul mul.assoc (of_num 1) one_mul mul_one mul.left_distrib mul.right_distrib
  zero_ne_one le le.refl @le.trans @le.antisymm lt lt_iff_le_and_ne @add_le_add_left
  @mul_nonneg @mul_pos le_iff_lt_or_eq le.total mul.comm

/- instantiate ordered ring theorems to int -/

namespace algebra
  open algebra
  instance [persistent] int.linear_ordered_comm_ring
end algebra

section port_algebra
  open algebra
  instance int.linear_ordered_comm_ring

  definition ge (a b : ℤ) := algebra.has_le.ge a b
  definition gt (a b : ℤ) := algebra.has_lt.gt a b
  infix >= := int.ge
  infix ≥  := int.ge
  infix >  := int.gt
  definition decidable_ge [instance] (a b : ℤ) : decidable (a ≥ b) := _
  definition decidable_gt [instance] (a b : ℤ) : decidable (a > b) := _

  theorem le_of_eq_of_le : ∀{a b c : ℤ}, a = b → b ≤ c → a ≤ c := @algebra.le_of_eq_of_le _ _
  theorem le_of_le_of_eq : ∀{a b c : ℤ}, a ≤ b → b = c → a ≤ c := @algebra.le_of_le_of_eq _ _
  theorem lt_of_eq_of_lt : ∀{a b c : ℤ}, a = b → b < c → a < c := @algebra.lt_of_eq_of_lt _ _
  theorem lt_of_lt_of_eq : ∀{a b c : ℤ}, a < b → b = c → a < c := @algebra.lt_of_lt_of_eq _ _
  calc_trans int.le_of_eq_of_le
  calc_trans int.le_of_le_of_eq
  calc_trans int.lt_of_eq_of_lt
  calc_trans int.lt_of_lt_of_eq

  theorem lt.asymm : ∀{a b : ℤ}, a < b → ¬ b < a := @algebra.lt.asymm _ _
  theorem lt_of_le_of_ne : ∀{a b : ℤ}, a ≤ b → a ≠ b → a < b := @algebra.lt_of_le_of_ne _ _
  theorem lt_of_lt_of_le : ∀{a b c : ℤ}, a < b → b ≤ c → a < c := @algebra.lt_of_lt_of_le _ _
  theorem lt_of_le_of_lt : ∀{a b c : ℤ}, a ≤ b → b < c → a < c := @algebra.lt_of_le_of_lt _ _
  theorem not_le_of_lt : ∀{a b : ℤ}, a < b → ¬ b ≤ a := @algebra.not_le_of_lt _ _
  theorem not_lt_of_le : ∀{a b : ℤ}, a ≤ b → ¬ b < a := @algebra.not_lt_of_le _ _

  theorem lt_or_eq_of_le : ∀{a b : ℤ}, a ≤ b → a < b ∨ a = b := @algebra.lt_or_eq_of_le _ _
  theorem lt.trichotomy : ∀a b : ℤ, a < b ∨ a = b ∨ b < a := algebra.lt.trichotomy
  theorem lt.by_cases : ∀{a b : ℤ} {P : Prop}, (a < b → P) → (a = b → P) → (b < a → P) → P :=
    @algebra.lt.by_cases _ _
  definition le_of_not_lt : ∀{a b : ℤ}, ¬ a < b → b ≤ a := @algebra.le_of_not_lt _ _
  definition lt_of_not_le : ∀{a b : ℤ}, ¬ a ≤ b → b < a := @algebra.lt_of_not_le _ _

  theorem add_le_add_right : ∀{a b : ℤ}, a ≤ b → ∀c : ℤ, a + c ≤ b + c :=
    @algebra.add_le_add_right _ _
  theorem add_le_add : ∀{a b c d : ℤ}, a ≤ b → c ≤ d → a + c ≤ b + d := @algebra.add_le_add _ _
  theorem add_lt_add_left : ∀{a b : ℤ}, a < b → ∀c : ℤ, c + a < c + b :=
    @algebra.add_lt_add_left _ _
  theorem add_lt_add_right : ∀{a b : ℤ}, a < b → ∀c : ℤ, a + c < b + c :=
    @algebra.add_lt_add_right _ _
  theorem le_add_of_nonneg_right : ∀{a b : ℤ}, b ≥ 0 → a ≤ a + b :=
    @algebra.le_add_of_nonneg_right _ _
  theorem le_add_of_nonneg_left : ∀{a b : ℤ}, b ≥ 0 → a ≤ b + a :=
    @algebra.le_add_of_nonneg_left _ _
  theorem add_lt_add : ∀{a b c d : ℤ}, a < b → c < d → a + c < b + d := @algebra.add_lt_add _ _
  theorem add_lt_add_of_le_of_lt : ∀{a b c d : ℤ}, a ≤ b → c < d → a + c < b + d :=
    @algebra.add_lt_add_of_le_of_lt _ _
  theorem add_lt_add_of_lt_of_le : ∀{a b c d : ℤ}, a < b → c ≤ d → a + c < b + d :=
    @algebra.add_lt_add_of_lt_of_le _ _
  theorem lt_add_of_pos_right : ∀{a b : ℤ}, b > 0 → a < a + b := @algebra.lt_add_of_pos_right _ _
  theorem lt_add_of_pos_left : ∀{a b : ℤ}, b > 0 → a < b + a := @algebra.lt_add_of_pos_left _ _
  theorem le_of_add_le_add_left : ∀{a b c : ℤ}, a + b ≤ a + c → b ≤ c :=
    @algebra.le_of_add_le_add_left _ _
  theorem le_of_add_le_add_right : ∀{a b c : ℤ}, a + b ≤ c + b → a ≤ c :=
    @algebra.le_of_add_le_add_right _ _
  theorem lt_of_add_lt_add_left : ∀{a b c : ℤ}, a + b < a + c → b < c :=
    @algebra.lt_of_add_lt_add_left _ _
  theorem lt_of_add_lt_add_right : ∀{a b c : ℤ}, a + b < c + b → a < c :=
    @algebra.lt_of_add_lt_add_right _ _
  theorem add_le_add_left_iff : ∀a b c : ℤ, a + b ≤ a + c ↔ b ≤ c := algebra.add_le_add_left_iff
  theorem add_le_add_right_iff : ∀a b c : ℤ, a + b ≤ c + b ↔ a ≤ c := algebra.add_le_add_right_iff
  theorem add_lt_add_left_iff : ∀a b c : ℤ, a + b < a + c ↔ b < c := algebra.add_lt_add_left_iff
  theorem add_lt_add_right_iff : ∀a b c : ℤ, a + b < c + b ↔ a < c := algebra.add_lt_add_right_iff
  theorem add_nonneg : ∀{a b : ℤ}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b := @algebra.add_nonneg _ _
  theorem add_pos : ∀{a b : ℤ}, 0 < a → 0 < b → 0 < a + b := @algebra.add_pos _ _
  theorem add_pos_of_pos_of_nonneg : ∀{a b : ℤ}, 0 < a → 0 ≤ b → 0 < a + b :=
    @algebra.add_pos_of_pos_of_nonneg _ _
  theorem add_pos_of_nonneg_of_pos : ∀{a b : ℤ}, 0 ≤ a → 0 < b → 0 < a + b :=
    @algebra.add_pos_of_nonneg_of_pos _ _
  theorem add_nonpos : ∀{a b : ℤ}, a ≤ 0 → b ≤ 0 → a + b ≤ 0 :=
    @algebra.add_nonpos _ _
  theorem add_neg : ∀{a b : ℤ}, a < 0 → b < 0 → a + b < 0 :=
    @algebra.add_neg _ _
  theorem add_neg_of_neg_of_nonpos : ∀{a b : ℤ}, a < 0 → b ≤ 0 → a + b < 0 :=
    @algebra.add_neg_of_neg_of_nonpos _ _
  theorem add_neg_of_nonpos_of_neg : ∀{a b : ℤ}, a ≤ 0 → b < 0 → a + b < 0 :=
    @algebra.add_neg_of_nonpos_of_neg _ _
  theorem add_eq_zero_iff_eq_zero_and_eq_zero_of_nonneg_of_nonneg : ∀{a b : ℤ},
    0 ≤ a → 0 ≤ b → a + b = 0 ↔ a = 0 ∧ b = 0 :=
    @algebra.add_eq_zero_iff_eq_zero_and_eq_zero_of_nonneg_of_nonneg _ _

  theorem le_add_of_nonneg_of_le : ∀{a b c : ℤ}, 0 ≤ a → b ≤ c → b ≤ a + c :=
    @algebra.le_add_of_nonneg_of_le _ _
  theorem le_add_of_le_of_nonneg : ∀{a b c : ℤ}, b ≤ c → 0 ≤ a → b ≤ c + a :=
    @algebra.le_add_of_le_of_nonneg _ _
  theorem lt_add_of_pos_of_le : ∀{a b c : ℤ}, 0 < a → b ≤ c → b < a + c :=
    @algebra.lt_add_of_pos_of_le _ _
  theorem lt_add_of_le_of_pos : ∀{a b c : ℤ}, b ≤ c → 0 < a → b < c + a :=
    @algebra.lt_add_of_le_of_pos _ _
  theorem add_le_of_nonpos_of_le : ∀{a b c : ℤ}, a ≤ 0 → b ≤ c → a + b ≤ c :=
    @algebra.add_le_of_nonpos_of_le _ _
  theorem add_le_of_le_of_nonpos : ∀{a b c : ℤ}, b ≤ c → a ≤ 0 → b + a ≤ c :=
    @algebra.add_le_of_le_of_nonpos _ _
  theorem add_lt_of_neg_of_le : ∀{a b c : ℤ}, a < 0 → b ≤ c → a + b < c :=
    @algebra.add_lt_of_neg_of_le _ _
  theorem add_lt_of_le_of_neg : ∀{a b c : ℤ}, b ≤ c → a < 0 → b + a < c :=
    @algebra.add_lt_of_le_of_neg _ _
  theorem lt_add_of_nonneg_of_lt : ∀{a b c : ℤ}, 0 ≤ a → b < c → b < a + c :=
    @algebra.lt_add_of_nonneg_of_lt _ _
  theorem lt_add_of_lt_of_nonneg : ∀{a b c : ℤ}, b < c → 0 ≤ a → b < c + a :=
    @algebra.lt_add_of_lt_of_nonneg _ _
  theorem lt_add_of_pos_of_lt : ∀{a b c : ℤ}, 0 < a → b < c → b < a + c :=
    @algebra.lt_add_of_pos_of_lt _ _
  theorem lt_add_of_lt_of_pos : ∀{a b c : ℤ}, b < c → 0 < a → b < c + a :=
    @algebra.lt_add_of_lt_of_pos _ _
  theorem add_lt_of_nonpos_of_lt : ∀{a b c : ℤ}, a ≤ 0 → b < c → a + b < c :=
    @algebra.add_lt_of_nonpos_of_lt _ _
  theorem add_lt_of_lt_of_nonpos : ∀{a b c : ℤ}, b < c →  a ≤ 0 → b + a < c :=
    @algebra.add_lt_of_lt_of_nonpos _ _
  theorem add_lt_of_neg_of_lt : ∀{a b c : ℤ}, a < 0 → b < c → a + b < c :=
    @algebra.add_lt_of_neg_of_lt _ _
  theorem add_lt_of_lt_of_neg : ∀{a b c : ℤ}, b < c → a < 0 → b + a < c :=
    @algebra.add_lt_of_lt_of_neg _ _

  theorem neg_le_neg : ∀{a b : ℤ}, a ≤ b → -b ≤ -a := @algebra.neg_le_neg _ _
  theorem neg_le_neg_iff_le : ∀a b : ℤ, -a ≤ -b ↔ b ≤ a := algebra.neg_le_neg_iff_le
  theorem neg_nonpos_iff_nonneg : ∀a : ℤ, -a ≤ 0 ↔ 0 ≤ a := algebra.neg_nonpos_iff_nonneg
  theorem neg_nonneg_iff_nonpos : ∀a : ℤ, 0 ≤ -a ↔ a ≤ 0 := algebra.neg_nonneg_iff_nonpos
  theorem neg_lt_neg : ∀{a b : ℤ}, a < b → -b < -a := @algebra.neg_lt_neg _ _
  theorem neg_lt_neg_iff_lt : ∀a b : ℤ, -a < -b ↔ b < a := algebra.neg_lt_neg_iff_lt
  theorem neg_neg_iff_pos : ∀a : ℤ, -a < 0 ↔ 0 < a := algebra.neg_neg_iff_pos
  theorem neg_pos_iff_neg : ∀a : ℤ, 0 < -a ↔ a < 0 := algebra.neg_pos_iff_neg
  theorem le_neg_iff_le_neg : ∀a b : ℤ, a ≤ -b ↔ b ≤ -a := algebra.le_neg_iff_le_neg
  theorem neg_le_iff_neg_le : ∀a b : ℤ, -a ≤ b ↔ -b ≤ a := algebra.neg_le_iff_neg_le
  theorem lt_neg_iff_lt_neg : ∀a b : ℤ, a < -b ↔ b < -a := algebra.lt_neg_iff_lt_neg
  theorem neg_lt_iff_neg_lt : ∀a b : ℤ, -a < b ↔ -b < a := algebra.neg_lt_iff_neg_lt
  theorem sub_nonneg_iff_le : ∀a b : ℤ, 0 ≤ a - b ↔ b ≤ a := algebra.sub_nonneg_iff_le
  theorem sub_nonpos_iff_le : ∀a b : ℤ, a - b ≤ 0 ↔ a ≤ b := algebra.sub_nonpos_iff_le
  theorem sub_pos_iff_lt : ∀a b : ℤ, 0 < a - b ↔ b < a := algebra.sub_pos_iff_lt
  theorem sub_neg_iff_lt : ∀a b : ℤ, a - b < 0 ↔ a < b := algebra.sub_neg_iff_lt
  theorem add_le_iff_le_neg_add : ∀a b c : ℤ, a + b ≤ c ↔ b ≤ -a + c :=
    algebra.add_le_iff_le_neg_add
  theorem add_le_iff_le_sub_left : ∀a b c : ℤ, a + b ≤ c ↔ b ≤ c - a :=
    algebra.add_le_iff_le_sub_left
  theorem add_le_iff_le_sub_right : ∀a b c : ℤ, a + b ≤ c ↔ a ≤ c - b :=
    algebra.add_le_iff_le_sub_right
  theorem le_add_iff_neg_add_le : ∀a b c : ℤ, a ≤ b + c ↔ -b + a ≤ c :=
    algebra.le_add_iff_neg_add_le
  theorem le_add_iff_sub_left_le : ∀a b c : ℤ, a ≤ b + c ↔ a - b ≤ c :=
    algebra.le_add_iff_sub_left_le
  theorem le_add_iff_sub_right_le : ∀a b c : ℤ, a ≤ b + c ↔ a - c ≤ b :=
    algebra.le_add_iff_sub_right_le
  theorem add_lt_iff_lt_neg_add_left : ∀a b c : ℤ, a + b < c ↔ b < -a + c :=
    algebra.add_lt_iff_lt_neg_add_left
  theorem add_lt_iff_lt_neg_add_right : ∀a b c : ℤ, a + b < c ↔ a < -b + c :=
    algebra.add_lt_iff_lt_neg_add_right
  theorem add_lt_iff_lt_sub_left : ∀a b c : ℤ, a + b < c ↔ b < c - a :=
    algebra.add_lt_iff_lt_sub_left
  theorem add_lt_add_iff_lt_sub_right : ∀a b c : ℤ, a + b < c ↔ a < c - b :=
    algebra.add_lt_add_iff_lt_sub_right
  theorem lt_add_iff_neg_add_lt_left : ∀a b c : ℤ, a < b + c ↔ -b + a < c :=
    algebra.lt_add_iff_neg_add_lt_left
  theorem lt_add_iff_neg_add_lt_right : ∀a b c : ℤ, a < b + c ↔ -c + a < b :=
    algebra.lt_add_iff_neg_add_lt_right
  theorem lt_add_iff_sub_lt_left : ∀a b c : ℤ, a < b + c ↔ a - b < c :=
    algebra.lt_add_iff_sub_lt_left
  theorem lt_add_iff_sub_lt_right : ∀a b c : ℤ, a < b + c ↔ a - c < b :=
    algebra.lt_add_iff_sub_lt_right
  theorem le_iff_le_of_sub_eq_sub : ∀{a b c d : ℤ}, a - b = c - d → a ≤ b ↔ c ≤ d :=
    @algebra.le_iff_le_of_sub_eq_sub _ _
  theorem lt_iff_lt_of_sub_eq_sub : ∀{a b c d : ℤ}, a - b = c - d → a < b ↔ c < d :=
    @algebra.lt_iff_lt_of_sub_eq_sub _ _
  theorem sub_le_sub_left : ∀{a b : ℤ}, a ≤ b → ∀c : ℤ, c - b ≤ c - a :=
    @algebra.sub_le_sub_left _ _
  theorem sub_le_sub_right : ∀{a b : ℤ}, a ≤ b → ∀c : ℤ, a - c ≤ b - c :=
    @algebra.sub_le_sub_right _ _
  theorem sub_le_sub : ∀{a b c d : ℤ}, a ≤ b → c ≤ d → a - d ≤ b - c :=
    @algebra.sub_le_sub _ _
  theorem sub_lt_sub_left : ∀{a b : ℤ}, a < b → ∀c : ℤ, c - b < c - a :=
    @algebra.sub_lt_sub_left _ _
  theorem sub_lt_sub_right : ∀{a b : ℤ}, a < b → ∀c : ℤ, a - c < b - c :=
    @algebra.sub_lt_sub_right _ _
  theorem sub_lt_sub : ∀{a b c d : ℤ}, a < b → c < d → a - d < b - c :=
    @algebra.sub_lt_sub _ _
  theorem sub_lt_sub_of_le_of_lt : ∀{a b c d : ℤ}, a ≤ b → c < d → a - d < b - c :=
    @algebra.sub_lt_sub_of_le_of_lt _ _
  theorem sub_lt_sub_of_lt_of_le : ∀{a b c d : ℤ}, a < b → c ≤ d → a - d < b - c :=
    @algebra.sub_lt_sub_of_lt_of_le _ _

  theorem mul_le_mul_of_nonneg_left : ∀{a b c : ℤ}, a ≤ b → 0 ≤ c → c * a ≤ c * b :=
    @algebra.mul_le_mul_of_nonneg_left _ _
  theorem mul_le_mul_of_nonneg_right : ∀{a b c : ℤ}, a ≤ b → 0 ≤ c → a * c ≤ b * c :=
    @algebra.mul_le_mul_of_nonneg_right _ _
  theorem mul_le_mul : ∀{a b c d : ℤ}, a ≤ c → b ≤ d → 0 ≤ b → 0 ≤ c → a * b ≤ c * d :=
    @algebra.mul_le_mul _ _
  theorem mul_nonpos_of_nonneg_of_nonpos : ∀{a b : ℤ}, a ≥ 0 → b ≤ 0 → a * b ≤ 0 :=
    @algebra.mul_nonpos_of_nonneg_of_nonpos _ _
  theorem mul_nonpos_of_nonpos_of_nonneg : ∀{a b : ℤ}, a ≤ 0 → b ≥ 0 → a * b ≤ 0 :=
    @algebra.mul_nonpos_of_nonpos_of_nonneg _ _
  theorem mul_lt_mul_of_pos_left : ∀{a b c : ℤ}, a < b → 0 < c → c * a < c * b :=
    @algebra.mul_lt_mul_of_pos_left _ _
  theorem mul_lt_mul_of_pos_right : ∀{a b c : ℤ}, a < b → 0 < c → a * c < b * c :=
    @algebra.mul_lt_mul_of_pos_right _ _
  theorem mul_lt_mul : ∀{a b c d : ℤ}, a < c → b ≤ d → 0 < b → 0 ≤ c → a * b < c * d :=
    @algebra.mul_lt_mul _ _
  theorem mul_neg_of_pos_of_neg : ∀{a b : ℤ}, a > 0 → b < 0 → a * b < 0 :=
    @algebra.mul_neg_of_pos_of_neg _ _
  theorem mul_neg_of_neg_of_pos : ∀{a b : ℤ}, a < 0 → b > 0 → a * b < 0 :=
    @algebra.mul_neg_of_neg_of_pos _ _
  theorem lt_of_mul_lt_mul_left : ∀{a b c : ℤ}, c * a < c * b → c ≥ zero → a < b :=
    @algebra.lt_of_mul_lt_mul_left int _
  theorem lt_of_mul_lt_mul_right : ∀{a b c : ℤ}, a * c < b * c → c ≥ 0 → a < b :=
    @algebra.lt_of_mul_lt_mul_right _ _
  theorem le_of_mul_le_mul_left : ∀{a b c : ℤ}, c * a ≤ c * b → c > 0 → a ≤ b :=
    @algebra.le_of_mul_le_mul_left _ _
  theorem le_of_mul_le_mul_right : ∀{a b c : ℤ}, a * c ≤ b * c → c > 0 → a ≤ b :=
    @algebra.le_of_mul_le_mul_right _ _
  theorem pos_of_mul_pos_left : ∀{a b : ℤ}, 0 < a * b → 0 ≤ a → 0 < b :=
    @algebra.pos_of_mul_pos_left _ _
  theorem pos_of_mul_pos_right : ∀{a b : ℤ}, 0 < a * b → 0 ≤ b → 0 < a :=
    @algebra.pos_of_mul_pos_right _ _

  theorem mul_le_mul_of_nonpos_left : ∀{a b c : ℤ}, b ≤ a → c ≤ 0 → c * a ≤ c * b :=
    @algebra.mul_le_mul_of_nonpos_left _ _
  theorem mul_le_mul_of_nonpos_right : ∀{a b c : ℤ}, b ≤ a → c ≤ 0 → a * c ≤ b * c :=
    @algebra.mul_le_mul_of_nonpos_right _ _
  theorem mul_nonneg_of_nonpos_of_nonpos : ∀{a b : ℤ}, a ≤ 0 → b ≤ 0 → 0 ≤ a * b :=
    @algebra.mul_nonneg_of_nonpos_of_nonpos _ _
  theorem mul_lt_mul_of_neg_left : ∀{a b c : ℤ}, b < a → c < 0 → c * a < c * b :=
    @algebra.mul_lt_mul_of_neg_left _ _
  theorem mul_lt_mul_of_neg_right : ∀{a b c : ℤ}, b < a → c < 0 → a * c < b * c :=
    @algebra.mul_lt_mul_of_neg_right _ _
  theorem mul_pos_of_neg_of_neg : ∀{a b : ℤ}, a < 0 → b < 0 → 0 < a * b :=
    @algebra.mul_pos_of_neg_of_neg _ _

  theorem mul_self_nonneg : ∀a : ℤ, a * a ≥ 0 := algebra.mul_self_nonneg
  theorem zero_le_one : #int 0 ≤ 1 := @algebra.zero_le_one int int.linear_ordered_comm_ring
  theorem zero_lt_one : #int 0 < 1 := @algebra.zero_lt_one int int.linear_ordered_comm_ring
  theorem pos_and_pos_or_neg_and_neg_of_mul_pos : ∀{a b : ℤ}, a * b > 0 →
    (a > 0 ∧ b > 0) ∨ (a < 0 ∧ b < 0) := @algebra.pos_and_pos_or_neg_and_neg_of_mul_pos _ _
end port_algebra

/- more facts specific to int -/

theorem nonneg_of_nat (n : ℕ) : 0 ≤ of_nat n := trivial

theorem exists_eq_of_nat {a : ℤ} (H : 0 ≤ a) : ∃n : ℕ, a = of_nat n :=
obtain (n : ℕ) (H1 : 0 + of_nat n = a), from le.elim H,
exists.intro n (!zero_add ▸ (H1⁻¹))

theorem exists_eq_neg_of_nat {a : ℤ} (H : a ≤ 0) : ∃n : ℕ, a = -(of_nat n) :=
have H2 : -a ≥ 0, from iff.mp' !neg_nonneg_iff_nonpos H,
obtain (n : ℕ) (Hn : -a = of_nat n), from exists_eq_of_nat H2,
exists.intro n (eq_neg_of_eq_neg (Hn⁻¹))

theorem of_nat_nat_abs_of_nonneg {a : ℤ} (H : a ≥ 0) : of_nat (nat_abs a) = a :=
obtain (n : ℕ) (Hn : a = of_nat n), from exists_eq_of_nat H,
Hn⁻¹ ▸ congr_arg of_nat (nat_abs_of_nat n)

theorem of_nat_nat_abs_of_nonpos {a : ℤ} (H : a ≤ 0) : of_nat (nat_abs a) = -a :=
have H1 : (-a) ≥ 0, from iff.mp' !neg_nonneg_iff_nonpos H,
calc
  of_nat (nat_abs a) = of_nat (nat_abs (-a)) : nat_abs_neg
                 ... = -a                    : of_nat_nat_abs_of_nonneg H1

exit











-- ### interaction with add

theorem le_add_of_nat_right (a : ℤ) (n : ℕ) : a ≤ a + n :=
le.intro (eq.refl (a + n))

theorem le_add_of_nat_left (a : ℤ) (n : ℕ) : a ≤ n + a :=
le.intro (add.comm a n)


theorem add_le_right {a b : ℤ} (H : a ≤ b) (c : ℤ) : a + c ≤ b + c :=
add.comm c b ▸ add.comm c a ▸ add_le_add_left H c

theorem add_le {a b c d : ℤ} (H1 : a ≤ b) (H2 : c ≤ d) : a + c ≤ b + d :=
le_trans (add_le_right H1 c) (add_le_add_left H2 b)

theorem add_le_cancel_right {a b c : ℤ} (H : a + c ≤ b + c) : a ≤ b :=
have H1 : a + c + -c ≤ b + c + -c, from add_le_right H (-c),
!add_neg_cancel_right ▸ !add_neg_cancel_right ▸ H1

theorem add_le_cancel_left {a b c : ℤ} (H : c + a ≤ c + b) : a ≤ b :=
add_le_cancel_right (add.comm c b ▸ add.comm c a ▸ H)

theorem add_le_inv {a b c d : ℤ} (H1 : a + b ≤ c + d) (H2 : c ≤ a) : b ≤ d :=
obtain (n : ℕ) (Hn : c + n = a), from le.elim H2,
have H3 : c + (n + b) ≤ c + d, from add.assoc c n b ▸ Hn⁻¹ ▸ H1,
have H4 : n + b ≤ d, from add_le_cancel_left H3,
show b ≤ d, from le_trans (le_add_of_nat_left b n) H4

theorem le_add_of_nat_right_trans {a b : ℤ} (H : a ≤ b) (n : ℕ) : a ≤ b + n :=
le_trans H (le_add_of_nat_right b n)

theorem le_imp_succ_le_or_eq {a b : ℤ} (H : a ≤ b) : a + 1 ≤ b ∨ a = b :=
obtain (n : ℕ) (Hn : a + n = b), from le.elim H,
discriminate
  (assume H2 : n = 0,
    have H3 : a = b, from
      calc
        a = a + 0 : (add_zero a)⁻¹
          ... = a + n : {H2⁻¹}
          ... = b : Hn,
    or.inr H3)
  (take k : ℕ,
    assume H2 : n = succ k,
    have H3 : a + 1 + k = b, from
      calc
        a + 1 + k = a + succ k : by simp
          ... = a + n : by simp
          ... = b : Hn,
    or.inl (le.intro H3))

-- ### interaction with neg and sub

theorem le_neg {a b : ℤ} (H : a ≤ b) : -b ≤ -a :=
obtain (n : ℕ) (Hn : a + n = b), from le.elim H,
have H2 : b - n = a, from (iff.mp !add_eq_iff_eq_add_neg Hn)⁻¹,
have H3 : -b + n = -a, from
  calc
    -b + n = -b + -(-n) : {(neg_neg n)⁻¹}
      ... = -(b + -n) : (neg_add_distrib b (-n))⁻¹
      ... = -a : {H2},
le.intro H3

theorem neg_le_zero {a : ℤ} (H : 0 ≤ a) : -a ≤ 0 :=
neg_zero ▸ (le_neg H)

theorem zero_le_neg {a : ℤ} (H : a ≤ 0) : 0 ≤ -a :=
neg_zero ▸ (le_neg H)

theorem le_neg_inv {a b : ℤ} (H : -a ≤ -b) : b ≤ a :=
neg_neg b ▸ neg_neg a ▸ le_neg H

theorem le_sub_of_nat (a : ℤ) (n : ℕ) : a - n ≤ a :=
le.intro (neg_add_cancel_right a n)

theorem sub_le_right {a b : ℤ} (H : a ≤ b) (c : ℤ) : a - c ≤ b - c :=
add_le_right H _

theorem sub_le_left {a b : ℤ} (H : a ≤ b) (c : ℤ) : c - b ≤ c - a :=
add_le_add_left (le_neg H) _

theorem sub_le {a b c d : ℤ} (H1 : a ≤ b) (H2 : d ≤ c) : a - c ≤ b - d :=
add_le H1 (le_neg H2)

theorem sub_le_right_inv {a b c : ℤ} (H : a - c ≤ b - c) : a ≤ b :=
add_le_cancel_right H

theorem sub_le_left_inv {a b c : ℤ} (H : c - a ≤ c - b) : b ≤ a :=
le_neg_inv (add_le_cancel_left H)

theorem le_iff_sub_nonneg (a b : ℤ) : a ≤ b ↔ 0 ≤ b - a :=
iff.intro
  (assume H, !sub_self ▸ sub_le_right H a)
  (assume H,
     have H1 : a ≤ b - a + a, from zero_add a ▸ add_le_right H a,
     !neg_add_cancel_right ▸ H1)


-- Less than, Greater than, Greater than or equal
-- ----------------------------------------------

definition ge (a b : ℤ) := b ≤ a
notation a >= b := int.ge a b
notation a ≥ b  := int.ge a b

definition gt (a b : ℤ) := b < a
notation a > b  := int.gt a b

theorem lt_def (a b : ℤ) : a < b ↔ a + 1 ≤ b :=
iff.refl (a < b)

theorem gt_def (n m : ℕ) : n > m ↔ m < n :=
iff.refl (n > m)

theorem ge_def (n m : ℕ) : n ≥ m ↔ m ≤ n :=
iff.refl (n ≥ m)

-- add_rewrite gt_def ge_def --it might be possible to remove this in Lean 0.2


-- -- ### basic facts

theorem gt_of_nat (n m : ℕ) : (of_nat n > of_nat m) ↔ (n > m) :=
of_nat_lt_of_nat m n

-- ### interaction with le


theorem le_imp_lt_or_eq {a b : ℤ} (H : a ≤ b) : a < b ∨ a = b :=
le_imp_succ_le_or_eq H

theorem le_ne_imp_lt {a b : ℤ} (H1 : a ≤ b)  (H2 : a ≠ b) : a < b :=
or_resolve_left (le_imp_lt_or_eq H1) H2

theorem le_imp_lt_succ {a b : ℤ} (H : a ≤ b) : a < b + 1 :=
add_le_right H 1

theorem lt_succ_imp_le {a b : ℤ} (H : a < b + 1) : a ≤ b :=
add_le_cancel_right H


-- ### transitivity, antisymmmetry

theorem lt_le_trans {a b c : ℤ} (H1 : a < b) (H2 : b ≤ c) : a < c :=
le_trans H1 H2

theorem le_lt_trans {a b c : ℤ} (H1 : a ≤ b) (H2 : b < c) : a < c :=
le_trans (add_le_right H1 1) H2

theorem lt_trans {a b c : ℤ} (H1 : a < b) (H2 : b < c) : a < c :=
lt_le_trans H1 (le_of_lt H2)

theorem le_imp_not_gt {a b : ℤ} (H : a ≤ b) : ¬ a > b :=
(assume H2 : a > b, absurd (le_lt_trans H H2) (lt.irrefl a))

theorem lt_imp_not_ge {a b : ℤ} (H : a < b) : ¬ a ≥ b :=
(assume H2 : a ≥ b, absurd (lt_le_trans H H2) (lt.irrefl a))

theorem lt_antisym {a b : ℤ} (H : a < b) : ¬ b < a :=
le_imp_not_gt (le_of_lt H)

-- ### interaction with addition

-- TODO: note: no longer works without the "show"
theorem add_lt_left {a b : ℤ} (H : a < b) (c : ℤ) : c + a < c + b :=
show (c + a) + 1 ≤ c + b, from (add.assoc c a 1)⁻¹ ▸ add_le_add_left H c

theorem add_lt_right {a b : ℤ} (H : a < b) (c : ℤ) : a + c < b + c :=
add.comm c b ▸ add.comm c a ▸ add_lt_left H c

theorem add_le_lt {a b c d : ℤ} (H1 : a ≤ c) (H2 : b < d) : a + b < c + d :=
le_lt_trans (add_le_right H1 b) (add_lt_left H2 c)

theorem add_lt_le {a b c d : ℤ} (H1 : a < c) (H2 : b ≤ d) : a + b < c + d :=
lt_le_trans (add_lt_right H1 b) (add_le_add_left H2 c)

theorem add_lt {a b c d : ℤ} (H1 : a < c) (H2 : b < d) : a + b < c + d :=
add_lt_le H1 (le_of_lt H2)

theorem add_lt_cancel_left {a b c : ℤ} (H : c + a < c + b) : a < b :=
show a + 1 ≤ b, from add_le_cancel_left (add.assoc c a 1 ▸ H)

theorem add_lt_cancel_right {a b c : ℤ} (H : a + c < b + c) : a < b :=
add_lt_cancel_left (add.comm b c ▸ add.comm a c ▸ H)

-- ### interaction with neg and sub

theorem lt_neg {a b : ℤ} (H : a < b) : -b < -a :=
have H2 : -(a + 1) + 1 = -a, by simp,
have H3 : -b ≤ -(a + 1), from le_neg H,
have H4 : -b + 1 ≤ -(a + 1) + 1, from add_le_right H3 1,
H2 ▸ H4

theorem neg_lt_zero {a : ℤ} (H : 0 < a) : -a < 0 :=
neg_zero ▸ lt_neg H

theorem zero_lt_neg {a : ℤ} (H : a < 0) : 0 < -a :=
neg_zero ▸ lt_neg H

theorem lt_neg_inv {a b : ℤ} (H : -a < -b) : b < a :=
neg_neg b ▸ neg_neg a ▸ lt_neg H

theorem lt_sub_of_nat_succ (a : ℤ) (n : ℕ) : a - succ n < a :=
lt.intro (neg_add_cancel_right a (succ n))

theorem sub_lt_right {a b : ℤ} (H : a < b) (c : ℤ) : a - c < b - c :=
add_lt_right H _

theorem sub_lt_left {a b : ℤ} (H : a < b) (c : ℤ) : c - b < c - a :=
add_lt_left (lt_neg H) _

theorem sub_lt {a b c d : ℤ} (H1 : a < b) (H2 : d < c) : a - c < b - d :=
add_lt H1 (lt_neg H2)

theorem sub_lt_right_inv {a b c : ℤ} (H : a - c < b - c) : a < b :=
add_lt_cancel_right H

theorem sub_lt_left_inv {a b c : ℤ} (H : c - a < c - b) : b < a :=
lt_neg_inv (add_lt_cancel_left H)

-- ### totality of lt and le

-- add_rewrite succ_pos zero_le --move some of these to nat.lean
-- add_rewrite le_of_nat lt_of_nat gt_of_nat --remove gt_of_nat in Lean 0.2
-- add_rewrite le_neg lt_neg neg_le_zero zero_le_neg zero_lt_neg neg_lt_zero

theorem neg_le_pos (n m : ℕ) : -n ≤ m :=
have H1 : of_nat 0 ≤ of_nat m, by simp,
have H2 : -n ≤ 0, by simp,
le_trans H2 H1

theorem le_or_gt (a b : ℤ) : a ≤ b ∨ a > b :=
by_cases_of_nat a
  (take n : ℕ,
    by_cases_of_nat_succ b
      (take m : ℕ,
        show of_nat n ≤ m ∨ of_nat n > m, from
        proof
          or.elim (@nat.le_or_gt n m)
            (assume H : n ≤ m, or.inl (iff.mp' !of_nat_le_of_nat H))
            (assume H : n > m, or.inr (iff.mp' !of_nat_lt_of_nat H))
        qed)
      (take m : ℕ,
        show n ≤ -succ m ∨ n > -succ m, from
          have H0 : -succ m < -m, from lt_neg ((of_nat_succ m)⁻¹ ▸ lt_succ m),
          have H : -succ m < n, from lt_le_trans H0 (neg_le_pos m n),
          or.inr H))
  (take n : ℕ,
    by_cases_of_nat_succ b
      (take m : ℕ,
        show -n ≤ m ∨ -n > m, from
          or.inl (neg_le_pos n m))
      (take m : ℕ,
         show -n ≤ -succ m ∨ -n > -succ m, from
          or_of_or_of_imp_of_imp le_or_gt
            (assume H : succ m ≤ n,
              le_neg (iff.elim_left (iff.symm (of_nat_le_of_nat (succ m) n)) H))
            (assume H : succ m > n,
              lt_neg (iff.elim_left (iff.symm (of_nat_lt_of_nat n (succ m))) H))))

theorem trichotomy_alt (a b : ℤ) : (a < b ∨ a = b) ∨ a > b :=
or_of_or_of_imp_left (le_or_gt a b) (assume H : a ≤ b, le_imp_lt_or_eq H)

theorem trichotomy (a b : ℤ) : a < b ∨ a = b ∨ a > b :=
iff.elim_left or.assoc (trichotomy_alt a b)

theorem le_total (a b : ℤ) : a ≤ b ∨ b ≤ a :=
or_of_or_of_imp_right (le_or_gt a b) (assume H : b < a, le_of_lt H)

theorem not_le_of_lt {a b : ℤ} (H : ¬ a < b) : b ≤ a :=
or_resolve_left (le_or_gt b a) H

theorem not_le_imp_lt {a b : ℤ} (H : ¬ a ≤ b) : b < a :=
or_resolve_right (le_or_gt a b) H

-- (non)positivity and (non)negativity
-- -------------------------------------

-- ### basic

-- see also "int_by_cases" and similar theorems

theorem pos_imp_exists_nat {a : ℤ} (H : a ≥ 0) : ∃n : ℕ, a = n :=
obtain (n : ℕ) (Hn : of_nat 0 + n = a), from le.elim H,
exists.intro n (Hn⁻¹ ⬝ zero_add n)

theorem neg_imp_exists_nat {a : ℤ} (H : a ≤ 0) : ∃n : ℕ, a = -n :=
have H2 : -a ≥ 0, from zero_le_neg H,
obtain (n : ℕ) (Hn : -a = n), from pos_imp_exists_nat H2,
have H3 : a = -n, from (eq_neg_of_eq_neg (Hn⁻¹)),
exists.intro n H3

theorem nat_abs_nonneg_eq {a : ℤ} (H : a ≥ 0) : (nat_abs a) = a :=
obtain (n : ℕ) (Hn : a = n), from pos_imp_exists_nat H,
Hn⁻¹ ▸ congr_arg of_nat (nat_abs_of_nat n)

theorem of_nat_nonneg (n : ℕ) : of_nat n ≥ 0 :=
iff.mp (iff.symm !of_nat_le_of_nat) !zero_le

definition ge_decidable [instance] {a b : ℤ} : decidable (a ≥ b) := _
definition lt_decidable [instance] {a b : ℤ} : decidable (a < b) := _
definition gt_decidable [instance] {a b : ℤ} : decidable (a > b) := _

--nat_abs_neg is already taken... rename?
theorem nat_abs_negative {a : ℤ} (H : a ≤ 0) : (nat_abs a) = -a :=
obtain (n : ℕ) (Hn : a = -n), from neg_imp_exists_nat H,
calc
  (nat_abs a) = (nat_abs (-n)) : {Hn}
  ... = (nat_abs n) : nat_abs_neg
  ... = n : {nat_abs_of_nat n}
  ... = -a : (eq_neg_of_eq_neg Hn)⁻¹

theorem nat_abs_cases (a : ℤ) : a = (nat_abs a) ∨ a = - (nat_abs a) :=
or_of_or_of_imp_of_imp (le_total 0 a)
  (assume H : a ≥ 0, (nat_abs_nonneg_eq H)⁻¹)
  (assume H : a ≤ 0, (eq_neg_of_eq_neg (nat_abs_negative H)))

-- ### interaction of mul with le and lt

theorem mul_le_left_nonneg {a b c : ℤ} (Ha : a ≥ 0) (H : b ≤ c) : a * b ≤ a * c :=
obtain (n : ℕ) (Hn : b + n = c), from le.elim H,
have H2 : a * b + of_nat ((nat_abs a) * n) = a * c, from
  calc
    a * b + of_nat ((nat_abs a) * n) = a * b + (nat_abs a) * of_nat n : by simp
      ... = a * b + a * n : {nat_abs_nonneg_eq Ha}
      ... = a * (b + n) : by simp
      ... = a * c : by simp,
le.intro H2

theorem mul_le_right_nonneg {a b c : ℤ} (Hb : b ≥ 0) (H : a ≤ c) : a * b ≤ c * b :=
!mul.comm ▸ !mul.comm ▸ mul_le_left_nonneg Hb H

theorem mul_le_left_nonpos {a b c : ℤ} (Ha : a ≤ 0) (H : b ≤ c) : a * c ≤ a * b :=
have H2 : -a * b ≤ -a * c, from mul_le_left_nonneg (zero_le_neg Ha) H,
have H3 : -(a * b) ≤ -(a * c), from !neg_mul_eq_neg_mul⁻¹ ▸ !neg_mul_eq_neg_mul⁻¹ ▸ H2,
le_neg_inv H3

theorem mul_le_right_nonpos {a b c : ℤ} (Hb : b ≤ 0) (H : c ≤ a) : a * b ≤ c * b :=
!mul.comm ▸ !mul.comm ▸ mul_le_left_nonpos Hb H

---this theorem can be made more general by replacing either Ha with 0 ≤ a or Hb with 0 ≤ d...
theorem mul_le_nonneg {a b c d : ℤ} (Ha : a ≥ 0) (Hb : b ≥ 0) (Hc : a ≤ c) (Hd : b ≤ d)
  : a * b ≤ c * d :=
le_trans (mul_le_right_nonneg Hb Hc) (mul_le_left_nonneg (le_trans Ha Hc) Hd)

theorem mul_le_nonpos {a b c d : ℤ} (Ha : a ≤ 0) (Hb :b ≤ 0) (Hc : c ≤ a) (Hd : d ≤ b)
  : a * b ≤ c * d :=
le_trans (mul_le_right_nonpos Hb Hc) (mul_le_left_nonpos (le_trans Hc Ha) Hd)

theorem mul_lt_left_pos {a b c : ℤ} (Ha : a > 0) (H : b < c) : a * b < a * c :=
have H2 : a * b < a * b + a, from add_zero (a * b) ▸ add_lt_left Ha (a * b),
have H3 : a * b + a ≤ a * c, from (by simp) ▸ mul_le_left_nonneg (le_of_lt Ha) H,
lt_le_trans H2 H3

theorem mul_lt_right_pos {a b c : ℤ} (Hb : b > 0) (H : a < c) : a * b < c * b :=
mul.comm b c ▸ mul.comm b a ▸ mul_lt_left_pos Hb H

theorem mul_lt_left_neg {a b c : ℤ} (Ha : a < 0) (H : b < c) : a * c < a * b :=
have H2 : -a * b < -a * c, from mul_lt_left_pos (zero_lt_neg Ha) H,
have H3 : -(a * b) < -(a * c), from !neg_mul_eq_neg_mul⁻¹ ▸ !neg_mul_eq_neg_mul⁻¹ ▸ H2,
lt_neg_inv H3

theorem mul_lt_right_neg {a b c : ℤ} (Hb : b < 0) (H : c < a) : a * b < c * b :=
!mul.comm ▸ !mul.comm ▸ mul_lt_left_neg Hb H

theorem mul_le_lt_pos {a b c d : ℤ} (Ha : a > 0) (Hb : b ≥ 0) (Hc : a ≤ c) (Hd : b < d)
  : a * b < c * d :=
le_lt_trans (mul_le_right_nonneg Hb Hc) (mul_lt_left_pos (lt_le_trans Ha Hc) Hd)

theorem mul_lt_le_pos {a b c d : ℤ} (Ha : a ≥ 0) (Hb : b > 0) (Hc : a < c) (Hd : b ≤ d)
  : a * b < c * d :=
lt_le_trans (mul_lt_right_pos Hb Hc) (mul_le_left_nonneg (le_trans Ha (le_of_lt Hc)) Hd)

theorem mul_lt_pos {a b c d : ℤ} (Ha : a > 0) (Hb : b > 0) (Hc : a < c) (Hd : b < d)
  : a * b < c * d :=
mul_lt_le_pos (le_of_lt Ha) Hb Hc (le_of_lt Hd)

theorem mul_lt_neg {a b c d : ℤ} (Ha : a < 0) (Hb : b < 0) (Hc : c < a) (Hd : d < b)
  : a * b < c * d :=
lt_trans (mul_lt_right_neg Hb Hc) (mul_lt_left_neg (lt_trans Hc Ha) Hd)

-- theorem mul_le_lt_neg and mul_lt_le_neg?

theorem mul_lt_cancel_left_nonneg {a b c : ℤ} (Hc : c ≥ 0) (H : c * a < c * b) : a < b :=
or.elim (le_or_gt b a)
  (assume H2 : b ≤ a,
    have H3 : c * b ≤ c * a, from mul_le_left_nonneg Hc H2,
    absurd H3 (lt_imp_not_ge H))
  (assume H2 : a < b, H2)

theorem mul_lt_cancel_right_nonneg {a b c : ℤ} (Hc : c ≥ 0) (H : a * c < b * c) : a < b :=
mul_lt_cancel_left_nonneg Hc (mul.comm b c ▸ mul.comm a c ▸ H)

theorem mul_lt_cancel_left_nonpos {a b c : ℤ} (Hc : c ≤ 0) (H : c * b < c * a) : a < b :=
have H2 : -(c * a) < -(c * b), from lt_neg H,
have H3 : -c * a < -c * b, from !neg_mul_eq_neg_mul ▸ !neg_mul_eq_neg_mul ▸ H2,
have H4 : -c ≥ 0, from zero_le_neg Hc,
mul_lt_cancel_left_nonneg H4 H3

theorem mul_lt_cancel_right_nonpos {a b c : ℤ} (Hc : c ≤ 0) (H : b * c < a * c) : a < b :=
mul_lt_cancel_left_nonpos Hc (!mul.comm ▸ !mul.comm ▸ H)

theorem mul_le_cancel_left_pos {a b c : ℤ} (Hc : c > 0) (H : c * a ≤ c * b) : a ≤ b :=
or.elim (le_or_gt a b)
  (assume H2 : a ≤ b, H2)
  (assume H2 : a > b,
    have H3 : c * a > c * b, from mul_lt_left_pos Hc H2,
    absurd H3 (le_imp_not_gt H))

theorem mul_le_cancel_right_pos {a b c : ℤ} (Hc : c > 0) (H : a * c ≤ b * c) : a ≤ b :=
mul_le_cancel_left_pos Hc (!mul.comm ▸ !mul.comm ▸ H)

theorem mul_le_cancel_left_neg {a b c : ℤ} (Hc : c < 0) (H : c * b ≤ c * a) : a ≤ b :=
have H2 : -(c * a) ≤ -(c * b), from le_neg H,
have H3 : -c * a ≤ -c * b,
  from neg_mul_eq_neg_mul c b ▸ neg_mul_eq_neg_mul c a ▸ H2,
have H4 : -c > 0, from zero_lt_neg Hc,
mul_le_cancel_left_pos H4 H3

theorem mul_le_cancel_right_neg {a b c : ℤ} (Hc : c < 0) (H : b * c ≤ a * c) : a ≤ b :=
mul_le_cancel_left_neg Hc (!mul.comm ▸ !mul.comm ▸ H)

theorem mul_eq_one_left {a b : ℤ} (H : a * b = 1) : a = 1 ∨ a = - 1 :=
have H2 : (nat_abs a) * (nat_abs b) = 1, from
  calc
    (nat_abs a) * (nat_abs b) = (nat_abs (a * b)) : !mul_nat_abs⁻¹
                        ... = (nat_abs 1)       : {H}
                        ... = 1                : nat_abs_of_nat 1,
have H3 : (nat_abs a) = 1, from mul_eq_one_left H2,
or_of_or_of_imp_of_imp (nat_abs_cases a)
  (assume H4 : a = (nat_abs a), H3 ▸ H4)
  (assume H4 : a = - (nat_abs a), H3 ▸ H4)

theorem mul_eq_one_right {a b : ℤ} (H : a * b = 1) : b = 1 ∨ b = - 1 :=
mul_eq_one_left (!mul.comm ▸ H)


-- sign function
-- -------------

definition sign (a : ℤ) : ℤ := if a > 0 then 1 else (if a < 0 then - 1 else 0)

theorem sign_pos {a : ℤ} (H : a > 0) : sign a = 1 :=
if_pos H

theorem sign_negative {a : ℤ} (H : a < 0) : sign a = - 1 :=
if_neg (lt_antisym H) ⬝ if_pos H

theorem sign_zero : sign 0 = 0 :=
if_neg (lt.irrefl 0) ⬝ if_neg (lt.irrefl 0)

-- add_rewrite sign_negative sign_pos nat_abs_negative nat_abs_nonneg_eq sign_zero mul_nat_abs

theorem mul_sign_nat_abs (a : ℤ) : sign a * (nat_abs a) = a :=
have temp1 : ∀a : ℤ, a < 0 → a ≤ 0, from take a, le_of_lt,
have temp2 : ∀a : ℤ, a > 0 → a ≥ 0, from take a, le_of_lt,
or.elim3 (trichotomy a 0)
  (assume H : a < 0, by simp)
  (assume H : a = 0, by simp)
  (assume H : a > 0, by simp)

-- TODO: show decidable for equality (and avoid classical library)
theorem sign_mul (a b : ℤ) : sign (a * b) = sign a * sign b :=
or.elim (em (a = 0))
  (assume Ha : a = 0, by simp)
  (assume Ha : a ≠ 0,
    or.elim (em (b = 0))
      (assume Hb : b = 0, by simp)
      (assume Hb : b ≠ 0,
        have H : sign (a * b) * (nat_abs (a * b)) = sign a * sign b  * (nat_abs (a * b)), from
          calc
            sign (a * b) * (nat_abs (a * b)) = a * b : mul_sign_nat_abs (a * b)
              ... = sign a * (nat_abs a) * b : {(mul_sign_nat_abs a)⁻¹}
              ... = sign a * (nat_abs a) * (sign b * (nat_abs b)) : {(mul_sign_nat_abs b)⁻¹}
              ... = sign a * sign b  * (nat_abs (a * b)) : by simp,
        have H2 : (nat_abs (a * b)) ≠ 0, from
          take H2', mul_ne_zero Ha Hb (nat_abs_eq_zero H2'),
        have H3 : (nat_abs (a * b)) ≠ of_nat 0, from mt of_nat_inj H2,
        mul.cancel_right H3 H))

theorem sign_idempotent (a : ℤ) : sign (sign a) = sign a :=
have temp : of_nat 1 > 0, from iff.elim_left (iff.symm (of_nat_lt_of_nat 0 1)) !succ_pos,
    --this should be done with simp
or.elim3 (trichotomy a 0) sorry sorry sorry
--  (by simp)
--  (by simp)
--  (by simp)

theorem sign_succ (n : ℕ) : sign (succ n) = 1 :=
sign_pos (iff.elim_left (iff.symm (of_nat_lt_of_nat 0 (succ n))) !succ_pos)
  --this should be done with simp

theorem sign_neg (a : ℤ) : sign (-a) = - sign a :=
have temp1 : a > 0 → -a < 0, from neg_lt_zero,
have temp2 : a < 0 → -a > 0, from zero_lt_neg,
or.elim3 (trichotomy a 0) sorry sorry sorry
--  (by simp)
--  (by simp)
--  (by simp)

-- add_rewrite sign_neg

theorem nat_abs_sign_ne_zero {a : ℤ} (H : a ≠ 0) : (nat_abs (sign a)) = 1 :=
or.elim3 (trichotomy a 0) sorry
--  (by simp)
  (assume H2 : a = 0, absurd H2 H)
  sorry
--  (by simp)

theorem sign_nat_abs (a : ℤ) : sign (nat_abs a) = nat_abs (sign a) :=
have temp1 : ∀a : ℤ, a < 0 → a ≤ 0, from take a, le_of_lt,
have temp2 : ∀a : ℤ, a > 0 → a ≥ 0, from take a, le_of_lt,
or.elim3 (trichotomy a 0) sorry sorry sorry
--  (by simp)
--  (by simp)
--  (by simp)

end int
