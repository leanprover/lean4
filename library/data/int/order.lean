/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
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

theorem of_nat_le_of_nat_of_le {m n : ℕ} (H : #nat m ≤ n) : of_nat m ≤ of_nat n :=
obtain (k : ℕ) (Hk : m + k = n), from nat.le.elim H,
le.intro (Hk ▸ (of_nat_add m k)⁻¹)

theorem le_of_of_nat_le_of_nat {m n : ℕ} (H : of_nat m ≤ of_nat n) : (#nat m ≤ n) :=
obtain (k : ℕ) (Hk : of_nat m + of_nat k = of_nat n), from le.elim H,
have H1 : m + k = n, from of_nat.inj (of_nat_add m k ⬝ Hk),
nat.le.intro H1

theorem of_nat_le_of_nat (m n : ℕ) : of_nat m ≤ of_nat n ↔ m ≤ n :=
iff.intro le_of_of_nat_le_of_nat of_nat_le_of_nat_of_le

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

theorem of_nat_lt_of_nat (n m : ℕ) : of_nat n < of_nat m ↔ n < m :=
calc
  of_nat n < of_nat m ↔ of_nat n + 1 ≤ of_nat m : iff.refl
    ... ↔ of_nat (nat.succ n) ≤ of_nat m        : of_nat_succ n ▸ !iff.refl
    ... ↔ nat.succ n ≤ m                        : of_nat_le_of_nat
    ... ↔ n < m                                 : iff.symm (lt_iff_succ_le _ _)

theorem lt_of_of_nat_lt_of_nat {m n : ℕ} (H : of_nat m < of_nat n) : #nat m < n :=
iff.mp !of_nat_lt_of_nat H

theorem of_nat_lt_of_nat_of_lt {m n : ℕ} (H : #nat m < n) : of_nat m < of_nat n :=
iff.mp' !of_nat_lt_of_nat H

/- show that the integers form an ordered additive group -/

theorem le.refl (a : ℤ) : a ≤ a :=
le.intro (add_zero a)

theorem le.trans {a b c : ℤ} (H1 : a ≤ b) (H2 : b ≤ c) : a ≤ c :=
obtain (n : ℕ) (Hn : a + n = b), from le.elim H1,
obtain (m : ℕ) (Hm : b + m = c), from le.elim H2,
have H3 : a + of_nat (n + m) = c, from
  calc
    a + of_nat (n + m) = a + (of_nat n + m) : {of_nat_add n m}
      ... = a + n + m : (add.assoc a n m)⁻¹
      ... = b + m : {Hn}
      ... = c : Hm,
le.intro H3

theorem le.antisymm : ∀ {a b : ℤ}, a ≤ b → b ≤ a → a = b :=
take a b : ℤ, assume (H₁ : a ≤ b) (H₂ : b ≤ a),
obtain (n : ℕ) (Hn : a + n = b), from le.elim H₁,
obtain (m : ℕ) (Hm : b + m = a), from le.elim H₂,
have H₃ : a + of_nat (n + m) = a + 0, from
  calc
    a + of_nat (n + m) = a + (of_nat n + m) : of_nat_add
      ... = a + n + m                       : add.assoc
      ... = b + m                           : Hn
      ... = a                               : Hm
      ... = a + 0                           : add_zero,
have H₄ : of_nat (n + m) = of_nat 0, from add.left_cancel H₃,
have H₅ : n + m = 0, from of_nat.inj H₄,
have H₆ : n = 0, from nat.eq_zero_of_add_eq_zero_right H₅,
show a = b, from
  calc
    a = a + 0        : add_zero
      ... = a + n    : H₆
      ... = b        : Hn

theorem lt.irrefl (a : ℤ) : ¬ a < a :=
(assume H : a < a,
  obtain (n : ℕ) (Hn : a + succ n = a), from lt.elim H,
  have H2 : a + succ n = a + 0, from
    calc
      a + succ n = a : Hn
        ... = a + 0 : by simp,
  have H3 : nat.succ n = 0, from add.left_cancel H2,
  have H4 : nat.succ n = 0, from of_nat.inj H3,
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
    obtain (k : ℕ) (Hk : n = nat.succ k), from nat.exists_eq_succ_of_ne_zero H3,
    lt.intro (Hk ▸ Hn))

theorem le_iff_lt_or_eq (a b : ℤ) : a ≤ b ↔ (a < b ∨ a = b) :=
iff.intro
  (assume H,
    by_cases
      (assume H1 : a = b, or.inr H1)
      (assume H1 : a ≠ b,
        obtain (n : ℕ) (Hn : a + n = b), from le.elim H,
        have H2 : n ≠ 0, from (assume H' : n = 0, H1 (!add_zero ▸ H' ▸ Hn)),
        obtain (k : ℕ) (Hk : n = nat.succ k), from nat.exists_eq_succ_of_ne_zero H2,
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
obtain (n : ℕ) (Hn : 0 + nat.succ n = a), from lt.elim Ha,
obtain (m : ℕ) (Hm : 0 + nat.succ m = b), from lt.elim Hb,
lt.intro
  (eq.symm
    (calc
      a * b = (0 + nat.succ n) * b                 : Hn
        ... = nat.succ n * b                       : nat.zero_add
        ... = nat.succ n * (0 + nat.succ m)            : {Hm⁻¹}
        ... = nat.succ n * nat.succ m                  : nat.zero_add
        ... = of_nat (nat.succ n * nat.succ m)         : of_nat_mul
        ... = of_nat (nat.succ n * m + nat.succ n)     : nat.mul_succ
        ... = of_nat (nat.succ (nat.succ n * m + n))   : nat.add_succ
        ... = 0 + nat.succ (nat.succ n * m + n)        : zero_add))

section migrate_algebra
  open [classes] algebra

  protected definition linear_ordered_comm_ring [reducible] :
    algebra.linear_ordered_comm_ring int :=
  ⦃algebra.linear_ordered_comm_ring, int.integral_domain,
    le               := le,
    le_refl          := le.refl,
    le_trans         := @le.trans,
    le_antisymm      := @le.antisymm,
    lt               := lt,
    lt_iff_le_and_ne := lt_iff_le_and_ne,
    add_le_add_left  := @add_le_add_left,
    mul_nonneg       := @mul_nonneg,
    mul_pos          := @mul_pos,
    le_iff_lt_or_eq  := le_iff_lt_or_eq,
    le_total         := le.total,
    zero_ne_one      := zero_ne_one⦄

  protected definition decidable_linear_ordered_comm_ring [reducible] :
    algebra.decidable_linear_ordered_comm_ring int :=
  ⦃algebra.decidable_linear_ordered_comm_ring,
    int.linear_ordered_comm_ring,
    decidable_lt := decidable_lt⦄

  local attribute int.integral_domain [instance]
  local attribute int.linear_ordered_comm_ring [instance]
  local attribute int.decidable_linear_ordered_comm_ring [instance]

  definition ge [reducible] (a b : ℤ) := algebra.has_le.ge a b
  definition gt [reducible] (a b : ℤ) := algebra.has_lt.gt a b
  infix >= := int.ge
  infix ≥  := int.ge
  infix >  := int.gt
  definition decidable_ge [instance] (a b : ℤ) : decidable (a ≥ b) :=
  show decidable (b ≤ a), from _
  definition decidable_gt [instance] (a b : ℤ) : decidable (a > b) :=
  show decidable (b < a), from _
  definition sign : ∀a : ℤ, ℤ := algebra.sign
  definition abs : ℤ → ℤ := algebra.abs

  migrate from algebra with int
  replacing has_le.ge → ge, has_lt.gt → gt, sign → sign, abs → abs, dvd → dvd, sub → sub

  attribute le.trans ge.trans lt.trans gt.trans [trans]
  attribute lt_of_lt_of_le lt_of_le_of_lt gt_of_gt_of_ge gt_of_ge_of_gt [trans]
end migrate_algebra

/- more facts specific to int -/

theorem of_nat_nonneg (n : ℕ) : 0 ≤ of_nat n := trivial

theorem of_nat_pos {n : ℕ} (Hpos : #nat n > 0) : of_nat n > 0 :=
of_nat_lt_of_nat_of_lt Hpos

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

theorem sign_of_succ (n : nat) : sign (nat.succ n) = 1 :=
sign_of_pos (of_nat_pos !nat.succ_pos)

theorem exists_eq_neg_succ_of_nat {a : ℤ} : a < 0 → ∃m : ℕ, a = -[m +1] :=
int.cases_on a
  (take m H, absurd (of_nat_nonneg m : 0 ≤ m) (not_le_of_gt H))
  (take m H, exists.intro m rfl)

end int
