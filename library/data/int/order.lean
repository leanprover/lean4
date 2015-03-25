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

private definition nonneg (a : ℤ) : Prop := int.cases_on a (take n, true) (take n, false)
definition le (a b : ℤ) : Prop := nonneg (sub b a)
definition lt (a b : ℤ) : Prop := le (add a 1) b

infix - := int.sub
infix <= := int.le
infix ≤  := int.le
infix <  := int.lt

local attribute nonneg [reducible]
private definition decidable_nonneg [instance] (a : ℤ) : decidable (nonneg a) := int.cases_on a _ _
definition decidable_le [instance] (a b : ℤ) : decidable (a ≤ b) := decidable_nonneg _
definition decidable_lt [instance] (a b : ℤ) : decidable (a < b) := decidable_nonneg _

private theorem nonneg.elim {a : ℤ} : nonneg a → ∃n : ℕ, a = n :=
int.cases_on a (take n H, exists.intro n rfl) (take n' H, false.elim H)

private theorem nonneg_or_nonneg_neg (a : ℤ) : nonneg a ∨ nonneg (-a) :=
int.cases_on a (take n, or.inl trivial) (take n, or.inr trivial)

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
    have H0 : -(b - a) = a - b, from neg_sub b a,
    have H1 : nonneg (a - b), from H0 ▸ H,    -- too bad: can't do it in one step
    or.inr H1)

theorem of_nat_le_of_nat {m n : ℕ} (H : #nat m ≤ n) : of_nat m ≤ of_nat n :=
obtain (k : ℕ) (Hk : m + k = n), from nat.le.elim H,
le.intro (Hk ▸ of_nat_add_of_nat m k)

theorem le_of_of_nat_le_of_nat {m n : ℕ} (H : of_nat m ≤ of_nat n) : (#nat m ≤ n) :=
obtain (k : ℕ) (Hk : of_nat m + of_nat k = of_nat n), from le.elim H,
have H1 : m + k = n, from of_nat.inj ((of_nat_add_of_nat m k)⁻¹ ⬝ Hk),
nat.le.intro H1

theorem of_nat_le_of_nat_iff (m n : ℕ) : of_nat m ≤ of_nat n ↔ m ≤ n :=
iff.intro le_of_of_nat_le_of_nat of_nat_le_of_nat

theorem lt_add_succ (a : ℤ) (n : ℕ) : a < a + succ n :=
le.intro (show a + 1 + n = a + succ n, from
  calc
    a + 1 + n = a + (1 + n) : add.assoc
      ... = a + (n + 1)     : nat.add.comm
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

theorem of_nat_lt_of_nat_iff (n m : ℕ) : of_nat n < of_nat m ↔ n < m :=
calc
  of_nat n < of_nat m ↔ of_nat n + 1 ≤ of_nat m : iff.refl
    ... ↔ of_nat (succ n) ≤ of_nat m            : of_nat_succ n ▸ !iff.refl
    ... ↔ succ n ≤ m                            : of_nat_le_of_nat_iff
    ... ↔ n < m                                 : iff.symm (lt_iff_succ_le _ _)

theorem lt_of_of_nat_lt_of_nat {m n : ℕ} (H : of_nat m < of_nat n) : #nat m < n :=
iff.mp !of_nat_lt_of_nat_iff H

theorem of_nat_lt_of_nat {m n : ℕ} (H : #nat m < n) : of_nat m < of_nat n :=
iff.mp' !of_nat_lt_of_nat_iff H

/- show that the integers form an ordered additive group -/

theorem le.refl (a : ℤ) : a ≤ a :=
le.intro (add_zero a)

theorem le.trans {a b c : ℤ} (H1 : a ≤ b) (H2 : b ≤ c) : a ≤ c :=
obtain (n : ℕ) (Hn : a + n = b), from le.elim H1,
obtain (m : ℕ) (Hm : b + m = c), from le.elim H2,
have H3 : a + of_nat (n + m) = c, from
  calc
    a + of_nat (n + m) = a + (of_nat n + m) : {(of_nat_add_of_nat n m)⁻¹}
      ... = a + n + m : (add.assoc a n m)⁻¹
      ... = b + m : {Hn}
      ... = c : Hm,
le.intro H3

theorem le.antisymm {a b : ℤ} (H1 : a ≤ b) (H2 : b ≤ a) : a = b :=
obtain (n : ℕ) (Hn : a + n = b), from le.elim H1,
obtain (m : ℕ) (Hm : b + m = a), from le.elim H2,
have H3 : a + of_nat (n + m) = a + 0, from
  calc
    a + of_nat (n + m) = a + (of_nat n + m) : {(of_nat_add_of_nat n m)⁻¹}
      ... = a + n + m : (add.assoc a n m)⁻¹
      ... = b + m : {Hn}
      ... = a : Hm
      ... = a + 0 : (add_zero a)⁻¹,
have H4 : of_nat (n + m) = of_nat 0, from add.left_cancel H3,
have H5 : n + m = 0, from of_nat.inj H4,
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
  have H4 : succ n = 0, from of_nat.inj H3,
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
        ... = n * b       : nat.zero_add
        ... = n * (0 + m) : {Hm⁻¹}
        ... = n * m       : nat.zero_add
        ... = 0 + n * m   : zero_add))

theorem mul_pos {a b : ℤ} (Ha : 0 < a) (Hb : 0 < b) : 0 < a * b :=
obtain (n : ℕ) (Hn : 0 + succ n = a), from lt.elim Ha,
obtain (m : ℕ) (Hm : 0 + succ m = b), from lt.elim Hb,
lt.intro
  (eq.symm
    (calc
      a * b = (0 + succ n) * b                 : Hn
        ... = succ n * b                       : nat.zero_add
        ... = succ n * (0 + succ m)            : {Hm⁻¹}
        ... = succ n * succ m                  : nat.zero_add
        ... = of_nat (succ n * succ m)         : of_nat_mul_of_nat
        ... = of_nat (succ n * m + succ n)     : nat.mul_succ
        ... = of_nat (succ (succ n * m + n))   : nat.add_succ
        ... = 0 + succ (succ n * m + n)        : zero_add))

section
  open [classes] algebra

  protected definition linear_ordered_comm_ring [instance] [reducible] :
    algebra.linear_ordered_comm_ring int :=
  ⦃algebra.linear_ordered_comm_ring, int.integral_domain,
    le               := le,
    le_refl          := le.refl,
    le_trans         := @le.trans,
    le_antisymm      := @le.antisymm,
    lt               := lt,
    lt_iff_le_ne     := lt_iff_le_and_ne,
    add_le_add_left  := @add_le_add_left,
    mul_nonneg       := @mul_nonneg,
    mul_pos          := @mul_pos,
    le_iff_lt_or_eq  := le_iff_lt_or_eq,
    le_total         := le.total,
    zero_ne_one      := zero_ne_one⦄

  protected definition decidable_linear_ordered_comm_ring [instance] [reducible] :
    algebra.decidable_linear_ordered_comm_ring int :=
  ⦃algebra.decidable_linear_ordered_comm_ring,
    int.linear_ordered_comm_ring,
    decidable_lt := decidable_lt⦄
end

/- instantiate ordered ring theorems to int -/

section port_algebra
  definition ge [reducible] (a b : ℤ) := algebra.has_le.ge a b
  definition gt [reducible] (a b : ℤ) := algebra.has_lt.gt a b
  infix >= := int.ge
  infix ≥  := int.ge
  infix >  := int.gt

  definition decidable_ge [instance] (a b : ℤ) : decidable (a ≥ b) :=
  show decidable (b ≤ a), from _
  definition decidable_gt [instance] (a b : ℤ) : decidable (a > b) :=
  show decidable (b < a), from _

  theorem le_of_eq_of_le : ∀{a b c : ℤ}, a = b → b ≤ c → a ≤ c := @algebra.le_of_eq_of_le _ _
  theorem le_of_le_of_eq : ∀{a b c : ℤ}, a ≤ b → b = c → a ≤ c := @algebra.le_of_le_of_eq _ _
  theorem lt_of_eq_of_lt : ∀{a b c : ℤ}, a = b → b < c → a < c := @algebra.lt_of_eq_of_lt _ _
  theorem lt_of_lt_of_eq : ∀{a b c : ℤ}, a < b → b = c → a < c := @algebra.lt_of_lt_of_eq _ _
  calc_trans int.le_of_eq_of_le
  calc_trans int.le_of_le_of_eq
  calc_trans int.lt_of_eq_of_lt
  calc_trans int.lt_of_lt_of_eq

  theorem ge_of_eq_of_ge : ∀{a b c : ℤ}, a = b → b ≥ c → a ≥ c := @algebra.ge_of_eq_of_ge _ _
  theorem ge_of_ge_of_eq : ∀{a b c : ℤ}, a ≥ b → b = c → a ≥ c := @algebra.ge_of_ge_of_eq _ _
  theorem gt_of_eq_of_gt : ∀{a b c : ℤ}, a = b → b > c → a > c := @algebra.gt_of_eq_of_gt _ _
  theorem gt_of_gt_of_eq : ∀{a b c : ℤ}, a > b → b = c → a > c := @algebra.gt_of_gt_of_eq _ _
  theorem ge.trans: ∀{a b c : ℤ}, a ≥ b → b ≥ c → a ≥ c := @algebra.ge.trans _ _
  theorem gt.trans: ∀{a b c : ℤ}, a ≥ b → b ≥ c → a ≥ c := @algebra.ge.trans _ _
  theorem gt_of_gt_of_ge : ∀{a b c : ℤ}, a > b → b ≥ c → a > c := @algebra.gt_of_gt_of_ge _ _
  theorem gt_of_ge_of_gt : ∀{a b c : ℤ}, a ≥ b → b > c → a > c := @algebra.gt_of_ge_of_gt _ _
  calc_trans int.ge_of_eq_of_ge
  calc_trans int.ge_of_ge_of_eq
  calc_trans int.gt_of_eq_of_gt
  calc_trans int.gt_of_gt_of_eq

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
  theorem le_of_not_lt : ∀{a b : ℤ}, ¬ a < b → b ≤ a := @algebra.le_of_not_lt _ _
  theorem lt_of_not_le : ∀{a b : ℤ}, ¬ a ≤ b → b < a := @algebra.lt_of_not_le _ _
  theorem lt_or_ge : ∀a b : ℤ, a < b ∨ a ≥ b := @algebra.lt_or_ge _ _
  theorem le_or_gt : ∀a b : ℤ, a ≤ b ∨ a > b := @algebra.le_or_gt _ _
  theorem lt_or_gt_of_ne : ∀{a b : ℤ}, a ≠ b → a < b ∨ a > b := @algebra.lt_or_gt_of_ne _ _

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
  theorem le_of_neg_le_neg : ∀{a b : ℤ}, -b ≤ -a → a ≤ b := @algebra.le_of_neg_le_neg _ _
  theorem neg_le_neg_iff_le : ∀a b : ℤ, -a ≤ -b ↔ b ≤ a := algebra.neg_le_neg_iff_le
  theorem nonneg_of_neg_nonpos : ∀{a : ℤ}, -a ≤ 0 → 0 ≤ a := @algebra.nonneg_of_neg_nonpos _ _
  theorem neg_nonpos_of_nonneg : ∀{a : ℤ}, 0 ≤ a → -a ≤ 0 := @algebra.neg_nonpos_of_nonneg _ _
  theorem neg_nonpos_iff_nonneg : ∀a : ℤ, -a ≤ 0 ↔ 0 ≤ a := algebra.neg_nonpos_iff_nonneg
  theorem nonpos_of_neg_nonneg : ∀{a : ℤ}, 0 ≤ -a → a ≤ 0 := @algebra.nonpos_of_neg_nonneg _ _
  theorem neg_nonneg_of_nonpos : ∀{a : ℤ}, a ≤ 0 → 0 ≤ -a := @algebra.neg_nonneg_of_nonpos _ _
  theorem neg_nonneg_iff_nonpos : ∀a : ℤ, 0 ≤ -a ↔ a ≤ 0 := algebra.neg_nonneg_iff_nonpos
  theorem neg_lt_neg : ∀{a b : ℤ}, a < b → -b < -a := @algebra.neg_lt_neg _ _
  theorem lt_of_neg_lt_neg : ∀{a b : ℤ}, -b < -a → a < b := @algebra.lt_of_neg_lt_neg _ _
  theorem neg_lt_neg_iff_lt : ∀a b : ℤ, -a < -b ↔ b < a := algebra.neg_lt_neg_iff_lt
  theorem pos_of_neg_neg : ∀{a : ℤ}, -a < 0 →  0 < a := @algebra.pos_of_neg_neg _ _
  theorem neg_neg_of_pos : ∀{a : ℤ}, 0 < a → -a < 0 := @algebra.neg_neg_of_pos _ _
  theorem neg_neg_iff_pos : ∀a : ℤ, -a < 0 ↔ 0 < a := algebra.neg_neg_iff_pos
  theorem neg_of_neg_pos : ∀{a : ℤ}, 0 < -a → a < 0 := @algebra.neg_of_neg_pos _ _
  theorem neg_pos_of_neg : ∀{a : ℤ}, a < 0 → 0 < -a := @algebra.neg_pos_of_neg _ _
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
  theorem sub_le_self : ∀(a : ℤ) {b : ℤ}, b ≥ 0 → a - b ≤ a := algebra.sub_le_self
  theorem sub_lt_self : ∀(a : ℤ) {b : ℤ}, b > 0 → a - b < a := algebra.sub_lt_self

  theorem eq_zero_of_neg_eq : ∀{a : ℤ}, -a = a → a = 0 := @algebra.eq_zero_of_neg_eq _ _
  definition abs : ℤ → ℤ := algebra.abs

  theorem abs_of_nonneg : ∀{a : ℤ}, a ≥ 0 → abs a = a := @algebra.abs_of_nonneg _ _
  theorem abs_of_pos : ∀{a : ℤ}, a > 0 → abs a = a := @algebra.abs_of_pos _ _
  theorem abs_of_neg : ∀{a : ℤ}, a < 0 → abs a = -a := @algebra.abs_of_neg _ _
  theorem abs_zero : abs 0 = 0 := algebra.abs_zero
  theorem abs_of_nonpos : ∀{a : ℤ}, a ≤ 0 → abs a = -a := @algebra.abs_of_nonpos _ _
  theorem abs_neg : ∀a : ℤ, abs (-a) = abs a := algebra.abs_neg
  theorem abs_nonneg : ∀a : ℤ, abs a ≥ 0 := algebra.abs_nonneg
  theorem abs_abs : ∀a : ℤ, abs (abs a) = abs a := algebra.abs_abs
  theorem le_abs_self : ∀a : ℤ, a ≤ abs a := algebra.le_abs_self
  theorem neg_le_abs_self : ∀a : ℤ, -a ≤ abs a := algebra.neg_le_abs_self
  theorem eq_zero_of_abs_eq_zero : ∀{a : ℤ}, abs a = 0 → a = 0 := @algebra.eq_zero_of_abs_eq_zero _ _
  theorem abs_eq_zero_iff_eq_zero : ∀a : ℤ, abs a = 0 ↔ a = 0 := algebra.abs_eq_zero_iff_eq_zero
  theorem abs_pos_of_pos : ∀{a : ℤ}, a > 0 → abs a > 0 := @algebra.abs_pos_of_pos _ _
  theorem abs_pos_of_neg : ∀{a : ℤ}, a < 0 → abs a > 0 := @algebra.abs_pos_of_neg _ _
  theorem abs_pos_of_ne_zero : ∀{a : ℤ}, a ≠ 0 → abs a > 0 := @algebra.abs_pos_of_ne_zero _ _
  theorem abs_sub : ∀a b : ℤ, abs (a - b) = abs (b - a) := algebra.abs_sub
  theorem abs.by_cases : ∀{P : ℤ → Prop}, ∀{a : ℤ}, P a → P (-a) → P (abs a) :=
    @algebra.abs.by_cases _ _
  theorem abs_le_of_le_of_neg_le : ∀{a b : ℤ}, a ≤ b → -a ≤ b → abs a ≤ b :=
    @algebra.abs_le_of_le_of_neg_le _ _
  theorem abs_lt_of_lt_of_neg_lt : ∀{a b : ℤ}, a < b → -a < b → abs a < b :=
    @algebra.abs_lt_of_lt_of_neg_lt _ _
  theorem abs_add_le_abs_add_abs : ∀a b : ℤ, abs (a + b) ≤ abs a + abs b :=
    algebra.abs_add_le_abs_add_abs
  theorem abs_sub_abs_le_abs_sub : ∀a b : ℤ, abs a - abs b ≤ abs (a - b) :=
    algebra.abs_sub_abs_le_abs_sub

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
  theorem lt_of_mul_lt_mul_left : ∀{a b c : ℤ}, c * a < c * b → c ≥ 0 → a < b :=
    @algebra.lt_of_mul_lt_mul_left _ _
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
  theorem zero_le_one : #int 0 ≤ 1 := trivial
  theorem zero_lt_one : #int 0 < 1 := trivial
  theorem pos_and_pos_or_neg_and_neg_of_mul_pos : ∀{a b : ℤ}, a * b > 0 →
    (a > 0 ∧ b > 0) ∨ (a < 0 ∧ b < 0) := @algebra.pos_and_pos_or_neg_and_neg_of_mul_pos _ _

  definition sign : ∀a : ℤ, ℤ := algebra.sign
  theorem sign_of_neg : ∀{a : ℤ}, a < 0 → sign a = -1 := @algebra.sign_of_neg _ _
  theorem sign_zero : sign 0 = 0 := algebra.sign_zero
  theorem sign_of_pos : ∀{a : ℤ}, a > 0 → sign a = 1 := @algebra.sign_of_pos _ _
  theorem sign_one : sign 1 = 1 := algebra.sign_one
  theorem sign_neg_one : sign (-1) = -1 := algebra.sign_neg_one
  theorem sign_sign : ∀a : ℤ, sign (sign a) = sign a := algebra.sign_sign
  theorem pos_of_sign_eq_one : ∀{a : ℤ}, sign a = 1 → a > 0 := @algebra.pos_of_sign_eq_one _ _
  theorem eq_zero_of_sign_eq_zero : ∀{a : ℤ}, sign a = 0 → a = 0 :=
    @algebra.eq_zero_of_sign_eq_zero _ _
  theorem neg_of_sign_eq_neg_one : ∀{a : ℤ}, sign a = -1 → a < 0 :=
    @algebra.neg_of_sign_eq_neg_one _ _
  theorem sign_neg : ∀a : ℤ, sign (-a) = -(sign a) := algebra.sign_neg
  theorem sign_mul : ∀a b : ℤ, sign (a * b) = sign a * sign b := algebra.sign_mul
  theorem abs_eq_sign_mul : ∀a : ℤ, abs a = sign a * a := algebra.abs_eq_sign_mul
  theorem eq_sign_mul_abs : ∀a : ℤ, a = sign a * abs a := algebra.eq_sign_mul_abs
  theorem abs_dvd_iff_dvd : ∀a b : ℤ, (abs a | b) ↔ (a | b) := algebra.abs_dvd_iff_dvd
  theorem dvd_abs_iff : ∀a b : ℤ, (a | abs b) ↔ (a | b) := algebra.dvd_abs_iff
  theorem abs_mul : ∀a b : ℤ, abs (a * b) = abs a * abs b := algebra.abs_mul
  theorem abs_mul_self : ∀a : ℤ, abs a * abs a = a * a := algebra.abs_mul_self
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

theorem of_nat_nat_abs (b : ℤ) : nat_abs b = abs b :=
or.elim (le.total 0 b)
  (assume H : b ≥ 0, of_nat_nat_abs_of_nonneg H ⬝ (abs_of_nonneg H)⁻¹)
  (assume H : b ≤ 0, of_nat_nat_abs_of_nonpos H ⬝ (abs_of_nonpos H)⁻¹)

theorem lt_of_add_one_le {a b : ℤ} (H : a + 1 ≤ b) : a < b :=
obtain n (H1 : a + 1 + n = b), from le.elim H,
have H2 : a + succ n = b, by rewrite [-H1, add.assoc, add.comm 1],
lt.intro H2

theorem add_one_le_of_lt {a b : ℤ} (H : a < b) : a + 1 ≤ b :=
obtain n (H1 : a + succ n = b), from lt.elim H,
have H2 : a + 1 + n = b, by rewrite [-H1, add.assoc, add.comm 1],
le.intro H2

theorem lt_add_one_of_le {a b : ℤ} (H : a ≤ b) : a < b + 1 :=
lt_add_of_le_of_pos H trivial

theorem le_of_lt_add_one {a b : ℤ} (H : a < b + 1) : a ≤ b :=
have H1 : a + 1 ≤ b + 1, from add_one_le_of_lt H,
le_of_add_le_add_right H1

theorem sub_one_le_of_lt {a b : ℤ} (H : a ≤ b) : a - 1 < b :=
lt_of_add_one_le (!sub_add_cancel⁻¹ ▸ H)

theorem lt_of_sub_one_le {a b : ℤ} (H : a - 1 < b) : a ≤ b :=
!sub_add_cancel ▸ add_one_le_of_lt H

theorem le_sub_one_of_lt {a b : ℤ} (H : a < b) : a ≤ b - 1 :=
le_of_lt_add_one (!sub_add_cancel⁻¹ ▸ H)

theorem lt_of_le_sub_one {a b : ℤ} (H : a ≤ b - 1) : a < b :=
!sub_add_cancel ▸ (lt_add_one_of_le H)

theorem of_nat_nonneg (n : ℕ) : of_nat n ≥ 0 := trivial

theorem of_nat_pos {n : ℕ} (Hpos : #nat n > 0) : of_nat n > 0 :=
of_nat_lt_of_nat Hpos

theorem sign_of_succ (n : nat) : sign (succ n) = 1 :=
sign_of_pos (of_nat_pos !nat.succ_pos)

theorem exists_eq_neg_succ_of_nat {a : ℤ} : a < 0 → ∃m : ℕ, a = -[m +1] :=
int.cases_on a
  (take m H, absurd (of_nat_nonneg m) (not_le_of_lt H))
  (take m H, exists.intro m rfl)

end int
