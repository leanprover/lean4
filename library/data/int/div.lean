/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: data.int.div
Author: Jeremy Avigad

Definitions and properties of div, mod, gcd, lcm, coprime. Following the SSReflect library
(and the SMT lib standard), we define a mod b so that 0 ≤ a mod b < |b| when b ≠ 0.
-/

import data.int.order data.nat.div
open [coercions] [reduce-hints] nat
open [declarations] nat (succ)
open eq.ops
notation `ℕ` := nat

set_option pp.beta true

namespace int

/- definitions -/

definition divide (a b : ℤ) : ℤ :=
sign b *
  (match a with
    of_nat m := #nat m div (nat_abs b),
    -[ m +1] := -[ (#nat m div (nat_abs b)) +1]
  end)

notation a div b := divide a b

definition modulo (a b : ℤ) : ℤ := a - a div b * b

notation a mod b := modulo a b

/- div  -/

theorem of_nat_div_of_nat (m n : nat) : m div n = of_nat (#nat m div n) :=
nat.cases_on n
  (by rewrite [↑divide, sign_zero, zero_mul, nat.div_zero])
  (take n, by rewrite [↑divide, sign_of_succ, one_mul])

theorem neg_succ_of_nat_div (m : nat) {b : ℤ} (H : b > 0) :
  -[m +1] div b = -(m div b + 1) :=
calc
  -[m +1] div b = sign b * _              : rfl
     ... = -[(#nat m div (nat_abs b)) +1] : by rewrite [(sign_of_pos H), one_mul]
     ... = -(m div b + 1)                 : by rewrite [↑divide, (sign_of_pos H), one_mul]

theorem div_neg (a b : ℤ) : a div -b = -(a div b) :=
calc
  a div -b = sign (-b) * _ : rfl
       ... = -(sign b) * _ : sign_neg
       ... = -(sign b * _) : neg_mul_eq_neg_mul
       ... = -(sign b * _) : nat_abs_neg
       ... = -(a div b)    : rfl

theorem zero_div (b : ℤ) : 0 div b = 0 :=
calc
  0 div b = sign b * (#nat 0 div (nat_abs b)) : rfl
      ... = sign b * 0 : nat.zero_div
      ... = 0          : mul_zero

theorem div_zero (a : ℤ) : a div 0 = 0 :=
by rewrite [↑divide, sign_zero, zero_mul]

theorem eq_div_mul_add_mod {a b : ℤ} : a = a div b * b + a mod b :=
!add.comm ▸ eq_add_of_sub_eq rfl

/- mod -/

theorem of_nat_mod_of_nat (m n : nat) : m mod n = (#nat m mod n) :=
have H : m = (#nat m mod n) + m div n * n, from calc
  m = of_nat (#nat m div n * n + m mod n)     : nat.eq_div_mul_add_mod
    ... = (#nat m div n) * n + (#nat m mod n) : rfl
    ... = m div n * n + (#nat m mod n)        : of_nat_div_of_nat
    ... = (#nat m mod n) + m div n * n        : add.comm,
calc
  m mod n = m - m div n * n : rfl
      ... = (#nat m mod n)  : sub_eq_of_eq_add H

theorem neg_succ_of_nat_mod (m : ℕ) {b : ℤ} (bpos : b > 0) :
  -[m +1] mod b = b - 1 - m mod b :=
calc
  -[m +1] mod b = -(m + 1) - -[m +1] div b * b : rfl
    ... = -(m + 1) - -(m div b + 1) * b        : neg_succ_of_nat_div _ bpos
    ... = -m + -1 + (b + m div b * b)          :
              by rewrite [neg_add, -neg_mul_eq_neg_mul, sub_neg_eq_add, mul.right_distrib,
                                 one_mul, (add.comm b)]
    ... = b + -1 + (-m + m div b * b)           :
              by rewrite [-*add.assoc, (add.comm (-m)), (add.right_comm (-1)), (add.comm b)]
    ... = b - 1 - m mod b                :
              by rewrite [↑modulo, *sub_eq_add_neg, neg_add, neg_neg]

theorem mod_neg (a b : ℤ) : a mod -b = a mod b :=
calc
  a mod -b = a - (a div -b) * -b : rfl
       ... = a - -(a div b) * -b : div_neg
       ... = a - a div b * b     : neg_mul_neg
       ... = a mod b             : rfl

theorem mod_abs (a b : ℤ) : a mod |b| = a mod b :=
abs.by_cases rfl !mod_neg

theorem zero_mod (b : ℤ) : 0 mod b = 0 :=
by rewrite [↑modulo, zero_div, zero_mul, sub_zero]

theorem mod_zero (a : ℤ) : a mod 0 = a :=
by rewrite [↑modulo, mul_zero, sub_zero]

private lemma of_nat_mod_abs (m : ℕ) (b : ℤ) : m mod |b| = (#nat m mod (nat_abs b)) :=
calc
  m mod |b| = m mod (nat_abs b)        : of_nat_nat_abs
        ... = (#nat m mod (nat_abs b)) : of_nat_mod_of_nat

private lemma of_nat_mod_abs_lt (m : ℕ) {b : ℤ} (H : b ≠ 0) : m mod |b| < |b| :=
have H1 : |b| > 0, from abs_pos_of_ne_zero H,
have H2 : (#nat nat_abs b > 0), from lt_of_of_nat_lt_of_nat (!of_nat_nat_abs⁻¹ ▸ H1),
calc
  m mod |b| = (#nat m mod (nat_abs b)) : of_nat_mod_abs m b
        ... < nat_abs b : of_nat_lt_of_nat (nat.mod_lt H2)
        ... = |b|       : of_nat_nat_abs _

theorem mod_nonneg (a : ℤ) {b : ℤ} (H : b ≠ 0) : a mod b ≥ 0 :=
have H1 : |b| > 0, from abs_pos_of_ne_zero H,
have H2 : a mod |b| ≥ 0, from
  int.cases_on a
    (take m, (of_nat_mod_abs m b)⁻¹ ▸ !of_nat_nonneg)
    (take m,
      have H3 : 1 + m mod |b| ≤ |b|, from (!add.comm ▸ add_one_le_of_lt (of_nat_mod_abs_lt m H)),
      calc
        -[ m +1] mod |b| = |b| - 1 - m mod |b| : neg_succ_of_nat_mod _ H1
          ... = |b| - (1 + m mod |b|)          : by rewrite [*sub_eq_add_neg, neg_add, add.assoc]
          ... ≥ 0                              : iff.mp' !sub_nonneg_iff_le H3),
!mod_abs ▸ H2

theorem mod_lt (a : ℤ) {b : ℤ} (H : b ≠ 0) : a mod b < |b| :=
have H1 : |b| > 0, from abs_pos_of_ne_zero H,
have H2 : a mod |b| < |b|, from
  int.cases_on a
    (take m, of_nat_mod_abs_lt m H)
    (take m,
      have H3 : |b| ≠ 0, from assume H', H (eq_zero_of_abs_eq_zero H'),
      have H4 : 1 + m mod |b| > 0, from add_pos_of_pos_of_nonneg dec_trivial (mod_nonneg _ H3),
      calc
        -[ m +1] mod |b| = |b| - 1 - m mod |b| : neg_succ_of_nat_mod _ H1
          ... = |b| - (1 + m mod |b|)          : by rewrite [*sub_eq_add_neg, neg_add, add.assoc]
          ... < |b|                            : sub_lt_self _ H4),
!mod_abs ▸ H2

/- both div and mod -/

private theorem add_mul_div_self_right_aux1 {a : ℤ} {k : ℕ} (n : ℕ) (H1 : a ≥ 0) (H2 : #nat k > 0) :
  (a + n * k) div k = a div k + n :=
obtain m (Hm : a = of_nat m), from exists_eq_of_nat H1,
Hm⁻¹ ▸ (calc
  (m + n * k) div k = (#nat (m + n * k)) div k : rfl
                ... = (#nat (m + n * k) div k) : of_nat_div_of_nat
                ... = (#nat m div k + n)       : !nat.add_mul_div_self_right H2
                ... = (#nat m div k) + n       : rfl
                ... = m div k + n : of_nat_div_of_nat)

private theorem add_mul_div_self_right_aux2 {a : ℤ} {k : ℕ} (n : ℕ) (H1 : a < 0) (H2 : #nat k > 0) :
  (a + n * k) div k = a div k + n :=
obtain m (Hm : a = -[m +1]), from exists_eq_neg_succ_of_nat H1,
or.elim (nat.lt_or_ge m (#nat n * k))
  (assume m_lt_nk : #nat m < n * k,
    have H3 : #nat (m + 1 ≤ n * k), from nat.succ_le_of_lt m_lt_nk,
    have H4 : #nat m div k + 1 ≤ n,
      from nat.succ_le_of_lt (nat.div_lt_of_lt_mul (!nat.mul.comm ▸ m_lt_nk)),
    Hm⁻¹ ▸ (calc
      (-[m +1] + n * k) div k = (n * k - (m + 1)) div k : by rewrite [add.comm, neg_succ_of_nat_eq]
        ... = ((#nat n * k) - (#nat m + 1)) div k       : rfl
        ... = (#nat n * k - (m + 1)) div k              : {of_nat_sub_of_nat H3}
        ... = #nat (n * k - (m + 1)) div k              : of_nat_div_of_nat
        ... = #nat (k * n - (m + 1)) div k              : nat.mul.comm
        ... = #nat n - m div k - 1                      :
                  nat.mul_sub_div_of_lt (!nat.mul.comm ▸ m_lt_nk)
        ... = #nat n - (m div k + 1)                    : nat.sub_sub
        ... = n - (#nat m div k + 1)                    : of_nat_sub_of_nat H4
        ... = -(m div k + 1) + n                        :
                  by rewrite [add.comm, -sub_eq_add_neg, -of_nat_add_of_nat, of_nat_div_of_nat]
        ... = -[m +1] div k + n                         :
                  neg_succ_of_nat_div m (of_nat_lt_of_nat H2)))
  (assume nk_le_m : #nat n * k ≤ m,
    eq.symm (Hm⁻¹ ▸ (calc
      -[m +1] div k + n = -(m div k + 1) + n              :
                  neg_succ_of_nat_div m (of_nat_lt_of_nat H2)
        ... = -((#nat m div k) + 1) + n                   : of_nat_div_of_nat
        ... = -((#nat (m - n * k + n * k) div k) + 1) + n : nat.sub_add_cancel nk_le_m
        ... = -((#nat (m - n * k) div k + n) + 1) + n     : nat.add_mul_div_self_right H2
        ... = -((#nat m - n * k) div k + 1)               :
                   by rewrite [-of_nat_add_of_nat, *neg_add, add.right_comm, neg_add_cancel_right,
                               of_nat_div_of_nat]
        ... = -[(#nat m - n * k) +1] div k                :
                   neg_succ_of_nat_div _ (of_nat_lt_of_nat H2)
        ... = -((#nat m - n * k) + 1) div k               : rfl
        ... = -(m - (#nat n * k) + 1) div k               : of_nat_sub_of_nat nk_le_m
        ... = (-(m + 1) + n * k) div k                    :
                   by rewrite [sub_eq_add_neg, -*add.assoc, *neg_add, neg_neg, add.right_comm]
        ... = (-[m +1] + n * k) div k                     : rfl)))

private theorem add_mul_div_self_right_aux3 (a : ℤ) {b c : ℤ} (H1 : b ≥ 0) (H2 : c > 0) :
    (a + b * c) div c = a div c + b :=
obtain n (Hn : b = of_nat n), from exists_eq_of_nat H1,
obtain k (Hk : c = of_nat k), from exists_eq_of_nat (le_of_lt H2),
have knz : k ≠ 0, from assume kz, !lt.irrefl (kz ▸ Hk ▸ H2),
have kgt0 : (#nat k > 0), from nat.pos_of_ne_zero knz,
have H3 : (a + n * k) div k = a div k + n, from
  or.elim (lt_or_ge a 0)
    (assume Ha : a < 0, add_mul_div_self_right_aux2 _ Ha kgt0)
    (assume Ha : a ≥ 0, add_mul_div_self_right_aux1 _ Ha kgt0),
Hn⁻¹ ▸ Hk⁻¹ ▸ H3

private theorem add_mul_div_self_right_aux4 (a b : ℤ) {c : ℤ} (H : c > 0) :
    (a + b * c) div c = a div c + b :=
or.elim (le.total 0 b)
  (assume H1 : 0 ≤ b, add_mul_div_self_right_aux3 _ H1 H)
  (assume H1 : 0 ≥ b,
    eq.symm (calc
      a div c + b = (a + b * c + -b * c) div c + b :
                        by rewrite [-neg_mul_eq_neg_mul, add_neg_cancel_right]
              ... = (a + b * c) div c + - b + b :
                        add_mul_div_self_right_aux3 _ (neg_nonneg_of_nonpos H1) H
              ... = (a + b * c) div c : neg_add_cancel_right))

theorem add_mul_div_self_right (a b : ℤ) {c : ℤ} (H : c ≠ 0) : (a + b * c) div c = a div c + b :=
lt.by_cases
  (assume H1 : 0 < c, !add_mul_div_self_right_aux4 H1)
  (assume H1 : 0 = c, absurd H1⁻¹ H)
  (assume H1 : 0 > c,
    have H2 : -c > 0, from neg_pos_of_neg H1,
    calc
      (a + b * c) div c = - ((a + -b * -c) div -c) : by rewrite [div_neg, neg_mul_neg, neg_neg]
                    ... = -(a div -c + -b)         : !add_mul_div_self_right_aux4 H2
                    ... = a div c + b              : by rewrite [div_neg, neg_add, *neg_neg])

end int
