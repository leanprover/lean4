-- Copyright (c) 2014 Floris van Doorn. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Floris van Doorn

-- int.order
-- =========

-- The order relation on the integers, and the sign function.

import .basic

using nat (hiding case)
using decidable
using fake_simplifier
using int

namespace int

-- ## le
definition le (a b : ℤ) : Prop := ∃n : ℕ, a + n = b
infix  `<=` := int.le
infix  `≤`  := int.le

theorem le_intro {a b : ℤ} {n : ℕ} (H : a + n = b) : a ≤ b :=
exists_intro n H

theorem le_elim {a b : ℤ} (H : a ≤ b) : ∃n : ℕ, a + n = b :=
H

-- ### partial order

theorem le_refl (a : ℤ) : a ≤ a :=
le_intro (add_zero_right a)

theorem le_of_nat (n m : ℕ) : (of_nat n ≤ of_nat m) ↔ (n ≤ m) :=
iff_intro
  (assume H : of_nat n ≤ of_nat m,
    obtain (k : ℕ) (Hk : of_nat n + of_nat k = of_nat m), from le_elim H,
    have H2 : n + k = m, from of_nat_inj (trans (symm (add_of_nat n k)) Hk),
    nat.le_intro H2)
  (assume H : n ≤ m,
    obtain (k : ℕ) (Hk : n + k = m), from nat.le_elim H,
    have H2 : of_nat n + of_nat k = of_nat m, from subst Hk (add_of_nat n k),
    le_intro H2)

theorem le_trans {a b c : ℤ} (H1 : a ≤ b) (H2 : b ≤ c) : a ≤ c :=
obtain (n : ℕ) (Hn : a + n = b), from le_elim H1,
obtain (m : ℕ) (Hm : b + m = c), from le_elim H2,
have H3 : a + of_nat (n + m) = c, from
  calc
    a + of_nat (n + m) = a + (of_nat n + m) : {symm (add_of_nat n m)}
      ... = a + n + m : symm (add_assoc a n m)
      ... = b + m : {Hn}
      ... = c : Hm,
le_intro H3

theorem le_antisym {a b : ℤ} (H1 : a ≤ b) (H2 : b ≤ a) : a = b :=
obtain (n : ℕ) (Hn : a + n = b), from le_elim H1,
obtain (m : ℕ) (Hm : b + m = a), from le_elim H2,
have H3 : a + of_nat (n + m) = a + 0, from
  calc
    a + of_nat (n + m) = a + (of_nat n + m) : {symm (add_of_nat n m)}
      ... = a + n + m : symm (add_assoc a n m)
      ... = b + m : {Hn}
      ... = a : Hm
      ... = a + 0 : symm (add_zero_right a),
have H4 : of_nat (n + m) = of_nat 0, from add_cancel_left H3,
have H5 : n + m = 0, from of_nat_inj H4,
have H6 : n = 0, from nat.add_eq_zero_left H5,
show a = b, from
  calc
    a = a + of_nat 0 : symm (add_zero_right a)
      ... = a + n : {symm H6}
      ... = b : Hn

-- ### interaction with add

theorem le_add_of_nat_right (a : ℤ) (n : ℕ) : a ≤ a + n :=
le_intro (refl (a + n))

theorem le_add_of_nat_left (a : ℤ) (n : ℕ) : a ≤ n + a :=
le_intro (add_comm a n)

theorem add_le_left {a b : ℤ} (H : a ≤ b) (c : ℤ) : c + a ≤ c + b :=
obtain (n : ℕ) (Hn : a + n = b), from le_elim H,
have H2 : c + a + n = c + b, from
  calc
    c + a + n = c + (a + n) : add_assoc c a n
      ... = c + b : {Hn},
le_intro H2

theorem add_le_right {a b : ℤ} (H : a ≤ b) (c : ℤ) : a + c ≤ b + c :=
subst (add_comm c b) (subst (add_comm c a) (add_le_left H c))

theorem add_le {a b c d : ℤ} (H1 : a ≤ b) (H2 : c ≤ d) : a + c ≤ b + d :=
le_trans (add_le_right H1 c) (add_le_left H2 b)

theorem add_le_cancel_right {a b c : ℤ} (H : a + c ≤ b + c) : a ≤ b :=
have H1 : a + c + -c ≤ b + c + -c, from add_le_right H (-c),
have H2 : a + c - c ≤ b + c - c, from subst (add_neg_right _ _) (subst (add_neg_right _ _) H1),
subst (add_sub_inverse b c) (subst (add_sub_inverse a c) H2)

theorem add_le_cancel_left {a b c : ℤ} (H : c + a ≤ c + b) : a ≤ b :=
add_le_cancel_right (subst (add_comm c b) (subst (add_comm c a) H))

theorem add_le_inv {a b c d : ℤ} (H1 : a + b ≤ c + d) (H2 : c ≤ a) : b ≤ d :=
obtain (n : ℕ) (Hn : c + n = a), from le_elim H2,
have H3 : c + (n + b) ≤ c + d, from subst (add_assoc c n b) (subst (symm Hn) H1),
have H4 : n + b ≤ d, from add_le_cancel_left H3,
show b ≤ d, from le_trans (le_add_of_nat_left b n) H4

theorem le_add_of_nat_right_trans {a b : ℤ} (H : a ≤ b) (n : ℕ) : a ≤ b + n :=
le_trans H (le_add_of_nat_right b n)

theorem le_imp_succ_le_or_eq {a b : ℤ} (H : a ≤ b) : a + 1 ≤ b ∨ a = b :=
obtain (n : ℕ) (Hn : a + n = b), from le_elim H,
discriminate
  (assume H2 : n = 0,
    have H3 : a = b, from
      calc
	a = a + 0 : symm (add_zero_right a)
	  ... = a + n : {symm H2}
	  ... = b : Hn,
    or_intro_right _ H3)
  (take k : ℕ,
    assume H2 : n = succ k,
    have H3 : a + 1 + k = b, from
      calc
	a + 1 + k = a + succ k : by simp
	  ... = a + n : by simp
	  ... = b : Hn,
    or_intro_left _ (le_intro H3))

-- ### interaction with neg and sub

theorem le_neg {a b : ℤ} (H : a ≤ b) : -b ≤ -a :=
obtain (n : ℕ) (Hn : a + n = b), from le_elim H,
have H2 : b - n = a, from add_imp_sub_right Hn,
have H3 : -b + n = -a, from
  calc
    -b + n = -b + -(-n) : {symm (neg_neg n)}
      ... = -(b + -n) : symm (neg_add_distr b (-n))
      ... = -(b - n) : {add_neg_right _ _}
      ... = -a : {H2},
le_intro H3

theorem neg_le_zero {a : ℤ} (H : 0 ≤ a) : -a ≤ 0 :=
subst neg_zero (le_neg H)

theorem zero_le_neg {a : ℤ} (H : a ≤ 0) : 0 ≤ -a :=
subst neg_zero (le_neg H)

theorem le_neg_inv {a b : ℤ} (H : -a ≤ -b) : b ≤ a :=
subst (neg_neg b) (subst (neg_neg a) (le_neg H))

theorem le_sub_of_nat (a : ℤ) (n : ℕ) : a - n ≤ a :=
le_intro (sub_add_inverse a n)

theorem sub_le_right {a b : ℤ} (H : a ≤ b) (c : ℤ) : a - c ≤ b - c :=
subst (add_neg_right _ _) (subst (add_neg_right _ _) (add_le_right H (-c)))

theorem sub_le_left {a b : ℤ} (H : a ≤ b) (c : ℤ) : c - b ≤ c - a :=
subst (add_neg_right _ _) (subst (add_neg_right _ _) (add_le_left (le_neg H) c))

theorem sub_le {a b c d : ℤ} (H1 : a ≤ b) (H2 : d ≤ c) : a - c ≤ b - d :=
subst (add_neg_right _ _) (subst (add_neg_right _ _) (add_le H1 (le_neg H2)))

theorem sub_le_right_inv {a b c : ℤ} (H : a - c ≤ b - c) : a ≤ b :=
add_le_cancel_right (subst (symm (add_neg_right _ _)) (subst (symm (add_neg_right _ _)) H))

theorem sub_le_left_inv {a b c : ℤ} (H : c - a ≤ c - b) : b ≤ a :=
le_neg_inv (add_le_cancel_left
    (subst (symm (add_neg_right _ _)) (subst (symm (add_neg_right _ _)) H)))

theorem le_iff_sub_nonneg (a b : ℤ) : a ≤ b ↔ 0 ≤ b - a :=
iff_intro
  (assume H, subst (sub_self _) (sub_le_right H a))
  (assume H, subst (sub_add_inverse _ _) (subst (add_zero_left _) (add_le_right H a)))


-- Less than, Greater than, Greater than or equal
-- ----------------------------------------------

definition lt (a b : ℤ) := a + 1 ≤ b
infix `<`  := int.lt

definition ge (a b : ℤ) := b ≤ a
infix `>=` := int.ge
infix `≥`  := int.ge

definition gt (a b : ℤ) := b < a
infix `>`  := int.gt

theorem lt_def (a b : ℤ) : a < b ↔ a + 1 ≤ b :=
iff_refl (a < b)

theorem gt_def (n m : ℕ) : n > m ↔ m < n :=
iff_refl (n > m)

theorem ge_def (n m : ℕ) : n ≥ m ↔ m ≤ n :=
iff_refl (n ≥ m)

-- add_rewrite gt_def ge_def --it might be possible to remove this in Lean 0.2

theorem lt_add_succ (a : ℤ) (n : ℕ) : a < a + succ n :=
le_intro (show a + 1 + n = a + succ n, by simp)

theorem lt_intro {a b : ℤ} {n : ℕ} (H : a + succ n = b) : a < b :=
subst H (lt_add_succ a n)

theorem lt_elim {a b : ℤ} (H : a < b) : ∃n : ℕ, a + succ n = b :=
obtain (n : ℕ) (Hn : a + 1 + n = b), from le_elim H,
have H2 : a + succ n = b, from
  calc
    a + succ n = a + 1 + n : by simp
      ... = b : Hn,
exists_intro n H2

-- -- ### basic facts

theorem lt_irrefl (a : ℤ) : ¬ a < a :=
not_intro
  (assume H : a < a,
    obtain (n : ℕ) (Hn : a + succ n = a), from lt_elim H,
    have H2 : a + succ n = a + 0, from
      calc
	a + succ n = a : Hn
	  ... = a + 0 : by simp,
    have H3 : succ n = 0, from add_cancel_left H2,
    have H4 : succ n = 0, from of_nat_inj H3,
    absurd H4 (succ_ne_zero n))

theorem lt_imp_ne {a b : ℤ} (H : a < b) : a ≠ b :=
not_intro (assume H2 : a = b, absurd (subst H2 H) (lt_irrefl b))

theorem lt_of_nat (n m : ℕ) : (of_nat n < of_nat m) ↔ (n < m) :=
calc
  (of_nat n + 1 ≤ of_nat m) ↔ (of_nat (succ n) ≤ of_nat m) : by simp
    ... ↔ (succ n ≤ m) : le_of_nat (succ n) m
    ... ↔ (n < m) : iff_symm (eq_to_iff (nat.lt_def n m))

theorem gt_of_nat (n m : ℕ) : (of_nat n > of_nat m) ↔ (n > m) :=
lt_of_nat m n

-- ### interaction with le

theorem lt_imp_le_succ {a b : ℤ} (H : a < b) : a + 1 ≤ b :=
H

theorem le_succ_imp_lt {a b : ℤ} (H : a + 1 ≤ b) : a < b :=
H

theorem self_lt_succ (a : ℤ) : a < a + 1 :=
le_refl (a + 1)

theorem lt_imp_le {a b : ℤ} (H : a < b) : a ≤ b :=
obtain (n : ℕ) (Hn : a + succ n = b), from lt_elim H,
le_intro Hn

theorem le_imp_lt_or_eq {a b : ℤ} (H : a ≤ b) : a < b ∨ a = b :=
le_imp_succ_le_or_eq H

theorem le_ne_imp_lt {a b : ℤ} (H1 : a ≤ b)  (H2 : a ≠ b) : a < b :=
resolve_left (le_imp_lt_or_eq H1) H2

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
lt_le_trans H1 (lt_imp_le H2)

theorem le_imp_not_gt {a b : ℤ} (H : a ≤ b) : ¬ a > b :=
not_intro (assume H2 : a > b, absurd (le_lt_trans H H2) (lt_irrefl a))

theorem lt_imp_not_ge {a b : ℤ} (H : a < b) : ¬ a ≥ b :=
not_intro (assume H2 : a ≥ b, absurd (lt_le_trans H H2) (lt_irrefl a))

theorem lt_antisym {a b : ℤ} (H : a < b) : ¬ b < a :=
le_imp_not_gt (lt_imp_le H)

-- ### interaction with addition

theorem add_lt_left {a b : ℤ} (H : a < b) (c : ℤ) : c + a < c + b :=
subst (symm (add_assoc c a 1)) (add_le_left H c)

theorem add_lt_right {a b : ℤ} (H : a < b) (c : ℤ) : a + c < b + c :=
subst (add_comm c b) (subst (add_comm c a) (add_lt_left H c))

theorem add_le_lt {a b c d : ℤ} (H1 : a ≤ c) (H2 : b < d) : a + b < c + d :=
le_lt_trans (add_le_right H1 b) (add_lt_left H2 c)

theorem add_lt_le {a b c d : ℤ} (H1 : a < c) (H2 : b ≤ d) : a + b < c + d :=
lt_le_trans (add_lt_right H1 b) (add_le_left H2 c)

theorem add_lt {a b c d : ℤ} (H1 : a < c) (H2 : b < d) : a + b < c + d :=
add_lt_le H1 (lt_imp_le H2)

theorem add_lt_cancel_left {a b c : ℤ} (H : c + a < c + b) : a < b :=
add_le_cancel_left (subst (add_assoc c a 1) (show c + a + 1 ≤ c + b, from H))

theorem add_lt_cancel_right {a b c : ℤ} (H : a + c < b + c) : a < b :=
add_lt_cancel_left (subst (add_comm b c) (subst (add_comm a c) H))


-- ### interaction with neg and sub

theorem lt_neg {a b : ℤ} (H : a < b) : -b < -a :=
have H2 : -(a + 1) + 1 = -a, by simp,
have H3 : -b ≤ -(a + 1), from le_neg H,
have H4 : -b + 1 ≤ -(a + 1) + 1, from add_le_right H3 1,
subst H2 H4

theorem neg_lt_zero {a : ℤ} (H : 0 < a) : -a < 0 :=
subst neg_zero (lt_neg H)

theorem zero_lt_neg {a : ℤ} (H : a < 0) : 0 < -a :=
subst neg_zero (lt_neg H)

theorem lt_neg_inv {a b : ℤ} (H : -a < -b) : b < a :=
subst (neg_neg b) (subst (neg_neg a) (lt_neg H))

theorem lt_sub_of_nat_succ (a : ℤ) (n : ℕ) : a - succ n < a :=
lt_intro (sub_add_inverse a (succ n))

theorem sub_lt_right {a b : ℤ} (H : a < b) (c : ℤ) : a - c < b - c :=
subst (add_neg_right _ _) (subst (add_neg_right _ _) (add_lt_right H (-c)))

theorem sub_lt_left {a b : ℤ} (H : a < b) (c : ℤ) : c - b < c - a :=
subst (add_neg_right _ _) (subst (add_neg_right _ _) (add_lt_left (lt_neg H) c))

theorem sub_lt {a b c d : ℤ} (H1 : a < b) (H2 : d < c) : a - c < b - d :=
subst (add_neg_right _ _) (subst (add_neg_right _ _) (add_lt H1 (lt_neg H2)))

theorem sub_lt_right_inv {a b c : ℤ} (H : a - c < b - c) : a < b :=
add_lt_cancel_right (subst (symm (add_neg_right _ _)) (subst (symm (add_neg_right _ _)) H))

theorem sub_lt_left_inv {a b c : ℤ} (H : c - a < c - b) : b < a :=
lt_neg_inv (add_lt_cancel_left
    (subst (symm (add_neg_right _ _)) (subst (symm (add_neg_right _ _)) H)))

-- ### totality of lt and le

-- add_rewrite succ_pos zero_le --move some of these to nat.lean
-- add_rewrite le_of_nat lt_of_nat gt_of_nat --remove gt_of_nat in Lean 0.2
-- add_rewrite le_neg lt_neg neg_le_zero zero_le_neg zero_lt_neg neg_lt_zero

theorem neg_le_pos (n m : ℕ) : -n ≤ m :=
have H1 : of_nat 0 ≤ of_nat m, by simp,
have H2 : -n ≤ 0, by simp,
le_trans H2 H1

theorem le_or_gt (a b : ℤ) : a ≤ b ∨ a > b :=
int_by_cases a
  (take n : ℕ,
    int_by_cases_succ b
      (take m : ℕ,
	show of_nat n ≤ m ∨ of_nat n > m, by simp) -- from (by simp) ◂ (le_or_gt n m))
      (take m : ℕ,
	show n ≤ -succ m ∨ n > -succ m, from
	  have H0 : -succ m < -m, from lt_neg (subst (symm (of_nat_succ m)) (self_lt_succ m)),
	  have H : -succ m < n, from lt_le_trans H0 (neg_le_pos m n),
	  or_intro_right _ H))
  (take n : ℕ,
    int_by_cases_succ b
      (take m : ℕ,
	show -n ≤ m ∨ -n > m, from
	  or_intro_left _ (neg_le_pos n m))
      (take m : ℕ,
	show -n ≤ -succ m ∨ -n > -succ m, from
	  or_imp_or (le_or_gt (succ m) n)
	    (assume H : succ m ≤ n,
	      le_neg (iff_elim_left (iff_symm (le_of_nat (succ m) n)) H))
	    (assume H : succ m > n,
	      lt_neg (iff_elim_left (iff_symm (lt_of_nat n (succ m))) H))))

theorem trichotomy_alt (a b : ℤ) : (a < b ∨ a = b) ∨ a > b :=
or_imp_or_left (le_or_gt a b) (assume H : a ≤ b, le_imp_lt_or_eq H)

theorem trichotomy (a b : ℤ) : a < b ∨ a = b ∨ a > b :=
iff_elim_left (or_assoc _ _ _) (trichotomy_alt a b)

theorem le_total (a b : ℤ) : a ≤ b ∨ b ≤ a :=
or_imp_or_right (le_or_gt a b) (assume H : b < a, lt_imp_le H)

theorem not_lt_imp_le {a b : ℤ} (H : ¬ a < b) : b ≤ a :=
resolve_left (le_or_gt b a) H

theorem not_le_imp_lt {a b : ℤ} (H : ¬ a ≤ b) : b < a :=
resolve_right (le_or_gt a b) H

-- (non)positivity and (non)negativity
-- -------------------------------------

-- ### basic

-- see also "int_by_cases" and similar theorems

theorem pos_imp_exists_nat {a : ℤ} (H : a ≥ 0) : ∃n : ℕ, a = n :=
obtain (n : ℕ) (Hn : of_nat 0 + n = a), from le_elim H,
exists_intro n (trans (symm Hn) (add_zero_left n))

theorem neg_imp_exists_nat {a : ℤ} (H : a ≤ 0) : ∃n : ℕ, a = -n :=
have H2 : -a ≥ 0, from zero_le_neg H,
obtain (n : ℕ) (Hn : -a = n), from pos_imp_exists_nat H2,
have H3 : a = -n, from symm (neg_move Hn),
exists_intro n H3

theorem to_nat_nonneg_eq {a : ℤ} (H : a ≥ 0) : (to_nat a) = a :=
obtain (n : ℕ) (Hn : a = n), from pos_imp_exists_nat H,
subst (symm Hn) (congr_arg of_nat (to_nat_of_nat n))

theorem of_nat_nonneg (n : ℕ) : of_nat n ≥ 0 :=
iff_mp (iff_symm (le_of_nat _ _)) (zero_le _)

theorem le_decidable [instance] {a b : ℤ} : decidable (a ≤ b) :=
have aux : ∀x, decidable (0 ≤ x), from
  take x,
    have H : 0 ≤ x ↔ of_nat (to_nat x) = x, from
      iff_intro
	(assume H1, to_nat_nonneg_eq H1)
	(assume H1, subst H1 (of_nat_nonneg (to_nat x))),
    decidable_iff_equiv _ (iff_symm H),
decidable_iff_equiv (aux _) (iff_symm (le_iff_sub_nonneg a b))

theorem ge_decidable [instance] {a b : ℤ} : decidable (a ≥ b)
theorem lt_decidable [instance] {a b : ℤ} : decidable (a < b)
theorem gt_decidable [instance] {a b : ℤ} : decidable (a > b)

--to_nat_neg is already taken... rename?
theorem to_nat_negative {a : ℤ} (H : a ≤ 0) : (to_nat a) = -a :=
obtain (n : ℕ) (Hn : a = -n), from neg_imp_exists_nat H,
calc
  (to_nat a) = (to_nat ( -n)) : {Hn}
  ... = (to_nat n) : {to_nat_neg n}
  ... = n : {to_nat_of_nat n}
  ... = -a : symm (neg_move (symm Hn))

theorem to_nat_cases (a : ℤ) : a = (to_nat a) ∨ a = - (to_nat a) :=
or_imp_or (le_total 0 a)
  (assume H : a ≥ 0, symm (to_nat_nonneg_eq H))
  (assume H : a ≤ 0, symm (neg_move (symm (to_nat_negative H))))

-- ### interaction of mul with le and lt

theorem mul_le_left_nonneg {a b c : ℤ} (Ha : a ≥ 0) (H : b ≤ c) : a * b ≤ a * c :=
obtain (n : ℕ) (Hn : b + n = c), from le_elim H,
have H2 : a * b + of_nat ((to_nat a) * n) = a * c, from
  calc
    a * b + of_nat ((to_nat a) * n) = a * b + (to_nat a) * of_nat n : by simp
      ... = a * b + a * n : {to_nat_nonneg_eq Ha}
      ... = a * (b + n) : by simp
      ... = a * c : by simp,
le_intro H2

theorem mul_le_right_nonneg {a b c : ℤ} (Hb : b ≥ 0) (H : a ≤ c) : a * b ≤ c * b :=
subst (mul_comm b c) (subst (mul_comm b a) (mul_le_left_nonneg Hb H))

theorem mul_le_left_nonpos {a b c : ℤ} (Ha : a ≤ 0) (H : b ≤ c) : a * c ≤ a * b :=
have H2 : -a * b ≤ -a * c, from mul_le_left_nonneg (zero_le_neg Ha) H,
have H3 : -(a * b) ≤ -(a * c), from subst (mul_neg_left a c) (subst (mul_neg_left a b) H2),
le_neg_inv H3

theorem mul_le_right_nonpos {a b c : ℤ} (Hb : b ≤ 0) (H : c ≤ a) : a * b ≤ c * b :=
subst (mul_comm b c) (subst (mul_comm b a) (mul_le_left_nonpos Hb H))

---this theorem can be made more general by replacing either Ha with 0 ≤ a or Hb with 0 ≤ d...
theorem mul_le_nonneg {a b c d : ℤ} (Ha : a ≥ 0) (Hb : b ≥ 0) (Hc : a ≤ c) (Hd : b ≤ d)
  : a * b ≤ c * d :=
le_trans (mul_le_right_nonneg Hb Hc) (mul_le_left_nonneg (le_trans Ha Hc) Hd)

theorem mul_le_nonpos {a b c d : ℤ} (Ha : a ≤ 0) (Hb : b ≤ 0) (Hc : c ≤ a) (Hd : d ≤ b)
  : a * b ≤ c * d :=
le_trans (mul_le_right_nonpos Hb Hc) (mul_le_left_nonpos (le_trans Hc Ha) Hd)

theorem mul_lt_left_pos {a b c : ℤ} (Ha : a > 0) (H : b < c) : a * b < a * c :=
have H2 : a * b < a * b + a, from subst (add_zero_right (a * b)) (add_lt_left Ha (a * b)),
have H3 : a * b + a ≤ a * c, from subst (by simp) (mul_le_left_nonneg (lt_imp_le Ha) H),
lt_le_trans H2 H3

theorem mul_lt_right_pos {a b c : ℤ} (Hb : b > 0) (H : a < c) : a * b < c * b :=
subst (mul_comm b c) (subst (mul_comm b a) (mul_lt_left_pos Hb H))

theorem mul_lt_left_neg {a b c : ℤ} (Ha : a < 0) (H : b < c) : a * c < a * b :=
have H2 : -a * b < -a * c, from mul_lt_left_pos (zero_lt_neg Ha) H,
have H3 : -(a * b) < -(a * c), from subst (mul_neg_left a c) (subst (mul_neg_left a b) H2),
lt_neg_inv H3

theorem mul_lt_right_neg {a b c : ℤ} (Hb : b < 0) (H : c < a) : a * b < c * b :=
subst (mul_comm b c) (subst (mul_comm b a) (mul_lt_left_neg Hb H))

theorem mul_le_lt_pos {a b c d : ℤ} (Ha : a > 0) (Hb : b ≥ 0) (Hc : a ≤ c) (Hd : b < d)
  : a * b < c * d :=
le_lt_trans (mul_le_right_nonneg Hb Hc) (mul_lt_left_pos (lt_le_trans Ha Hc) Hd)

theorem mul_lt_le_pos {a b c d : ℤ} (Ha : a ≥ 0) (Hb : b > 0) (Hc : a < c) (Hd : b ≤ d)
  : a * b < c * d :=
lt_le_trans (mul_lt_right_pos Hb Hc) (mul_le_left_nonneg (le_trans Ha (lt_imp_le Hc)) Hd)

theorem mul_lt_pos {a b c d : ℤ} (Ha : a > 0) (Hb : b > 0) (Hc : a < c) (Hd : b < d)
  : a * b < c * d :=
mul_lt_le_pos (lt_imp_le Ha) Hb Hc (lt_imp_le Hd)

theorem mul_lt_neg {a b c d : ℤ} (Ha : a < 0) (Hb : b < 0) (Hc : c < a) (Hd : d < b)
  : a * b < c * d :=
lt_trans (mul_lt_right_neg Hb Hc) (mul_lt_left_neg (lt_trans Hc Ha) Hd)

-- theorem mul_le_lt_neg and mul_lt_le_neg?

theorem mul_lt_cancel_left_nonneg {a b c : ℤ} (Hc : c ≥ 0) (H : c * a < c * b) : a < b :=
or_elim (le_or_gt b a)
  (assume H2 : b ≤ a,
    have H3 : c * b ≤ c * a, from mul_le_left_nonneg Hc H2,
    absurd H3 (lt_imp_not_ge H))
  (assume H2 : a < b, H2)

theorem mul_lt_cancel_right_nonneg {a b c : ℤ} (Hc : c ≥ 0) (H : a * c < b * c) : a < b :=
mul_lt_cancel_left_nonneg Hc (subst (mul_comm b c) (subst (mul_comm a c) H))

theorem mul_lt_cancel_left_nonpos {a b c : ℤ} (Hc : c ≤ 0) (H : c * b < c * a) : a < b :=
have H2 : -(c * a) < -(c * b), from lt_neg H,
have H3 : -c * a < -c * b,
  from subst (symm (mul_neg_left c b)) (subst (symm (mul_neg_left c a)) H2),
have H4 : -c ≥ 0, from zero_le_neg Hc,
mul_lt_cancel_left_nonneg H4 H3

theorem mul_lt_cancel_right_nonpos {a b c : ℤ} (Hc : c ≤ 0) (H : b * c < a * c) : a < b :=
mul_lt_cancel_left_nonpos Hc (subst (mul_comm b c) (subst (mul_comm a c) H))

theorem mul_le_cancel_left_pos {a b c : ℤ} (Hc : c > 0) (H : c * a ≤ c * b) : a ≤ b :=
or_elim (le_or_gt a b)
  (assume H2 : a ≤ b, H2)
  (assume H2 : a > b,
    have H3 : c * a > c * b, from mul_lt_left_pos Hc H2,
    absurd H3 (le_imp_not_gt H))

theorem mul_le_cancel_right_pos {a b c : ℤ} (Hc : c > 0) (H : a * c ≤ b * c) : a ≤ b :=
mul_le_cancel_left_pos Hc (subst (mul_comm b c) (subst (mul_comm a c) H))

theorem mul_le_cancel_left_neg {a b c : ℤ} (Hc : c < 0) (H : c * b ≤ c * a) : a ≤ b :=
have H2 : -(c * a) ≤ -(c * b), from le_neg H,
have H3 : -c * a ≤ -c * b,
  from subst (symm (mul_neg_left c b)) (subst (symm (mul_neg_left c a)) H2),
have H4 : -c > 0, from zero_lt_neg Hc,
mul_le_cancel_left_pos H4 H3

theorem mul_le_cancel_right_neg {a b c : ℤ} (Hc : c < 0) (H : b * c ≤ a * c) : a ≤ b :=
mul_le_cancel_left_neg Hc (subst (mul_comm b c) (subst (mul_comm a c) H))

theorem mul_eq_one_left {a b : ℤ} (H : a * b = 1) : a = 1 ∨ a = - 1 :=
have H2 : (to_nat a) * (to_nat b) = 1, from
  calc
    (to_nat a) * (to_nat b) = (to_nat (a * b)) : symm (mul_to_nat a b)
      ... = (to_nat 1) : {H}
      ... = 1 : to_nat_of_nat 1,
have H3 : (to_nat a) = 1, from mul_eq_one_left H2,
or_imp_or (to_nat_cases a)
  (assume H4 : a = (to_nat a), subst H3 H4)
  (assume H4 : a = - (to_nat a), subst H3 H4)

theorem mul_eq_one_right {a b : ℤ} (H : a * b = 1) : b = 1 ∨ b = - 1 :=
mul_eq_one_left (subst (mul_comm a b) H)


-- sign function
-- -------------

definition sign (a : ℤ) : ℤ := if a > 0 then 1 else (if a < 0 then - 1 else 0)

-- TODO: for kernel
theorem or_elim3 {a b c d : Prop} (H : a ∨ b ∨ c) (Ha : a → d) (Hb : b → d) (Hc : c → d) : d :=
or_elim H Ha (assume H2,or_elim H2 Hb Hc)

theorem sign_pos {a : ℤ} (H : a > 0) : sign a = 1 :=
if_pos H _ _

theorem sign_negative {a : ℤ} (H : a < 0) : sign a = - 1 :=
trans (if_neg (lt_antisym H) _ _) (if_pos H  _ _)

theorem sign_zero : sign 0 = 0 :=
trans (if_neg (lt_irrefl 0) _ _) (if_neg (lt_irrefl 0)  _ _)

-- add_rewrite sign_negative sign_pos to_nat_negative to_nat_nonneg_eq sign_zero mul_to_nat

theorem mul_sign_to_nat (a : ℤ) : sign a * (to_nat a) = a :=
have temp1 : ∀a : ℤ, a < 0 → a ≤ 0, from take a, lt_imp_le,
have temp2 : ∀a : ℤ, a > 0 → a ≥ 0, from take a, lt_imp_le,
or_elim3 (trichotomy a 0)
  (assume H : a < 0, by simp)
  (assume H : a = 0, by simp)
  (assume H : a > 0, by simp)

-- TODO: show decidable for equality (and avoid classical library)
theorem sign_mul (a b : ℤ) : sign (a * b) = sign a * sign b :=
or_elim (em (a = 0))
  (assume Ha : a = 0, by simp)
  (assume Ha : a ≠ 0,
    or_elim (em (b = 0))
      (assume Hb : b = 0, by simp)
      (assume Hb : b ≠ 0,
	have H : sign (a * b) * (to_nat (a * b)) = sign a * sign b  * (to_nat (a * b)), from
	  calc
	    sign (a * b) * (to_nat (a * b)) = a * b : mul_sign_to_nat (a * b)
	      ... = sign a * (to_nat a) * b : {symm (mul_sign_to_nat a)}
	      ... = sign a * (to_nat a) * (sign b * (to_nat b)) : {symm (mul_sign_to_nat b)}
	      ... = sign a * sign b  * (to_nat (a * b)) : by simp,
	have H2 : (to_nat (a * b)) ≠ 0, from
	  take H2', mul_ne_zero Ha Hb (to_nat_eq_zero H2'),
	have H3 : (to_nat (a * b)) ≠ of_nat 0, from mt of_nat_inj H2,
	mul_cancel_right H3 H))

--set_option pp::coercion true

theorem sign_idempotent (a : ℤ) : sign (sign a) = sign a :=
have temp : of_nat 1 > 0, from iff_elim_left (iff_symm (lt_of_nat 0 1)) (succ_pos 0),
    --this should be done with simp
or_elim3 (trichotomy a 0) sorry sorry sorry
--  (by simp)
--  (by simp)
--  (by simp)

theorem sign_succ (n : ℕ) : sign (succ n) = 1 :=
sign_pos (iff_elim_left (iff_symm (lt_of_nat 0 (succ n))) (succ_pos n))
  --this should be done with simp

theorem sign_neg (a : ℤ) : sign (-a) = - sign a :=
have temp1 : a > 0 → -a < 0, from neg_lt_zero,
have temp2 : a < 0 → -a > 0, from zero_lt_neg,
or_elim3 (trichotomy a 0) sorry sorry sorry
--  (by simp)
--  (by simp)
--  (by simp)

-- add_rewrite sign_neg

theorem to_nat_sign_ne_zero {a : ℤ} (H : a ≠ 0) : (to_nat (sign a)) = 1 :=
or_elim3 (trichotomy a 0) sorry
--  (by simp)
  (assume H2 : a = 0, absurd H2 H)
  sorry
--  (by simp)

theorem sign_to_nat (a : ℤ) : sign (to_nat a) = to_nat (sign a) :=
have temp1 : ∀a : ℤ, a < 0 → a ≤ 0, from take a, lt_imp_le,
have temp2 : ∀a : ℤ, a > 0 → a ≥ 0, from take a, lt_imp_le,
or_elim3 (trichotomy a 0) sorry sorry sorry
--  (by simp)
--  (by simp)
--  (by simp)

end int
