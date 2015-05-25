/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

Definitions and properties of div, mod, gcd, lcm, coprime, following the SSReflect library.

Following SSReflect and the SMTlib standard, we define a mod b so that 0 ≤ a mod b < |b| when b ≠ 0.
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
    | of_nat m := #nat m div (nat_abs b)
    | -[ m +1] := -[ (#nat m div (nat_abs b)) +1]
  end)

notation a div b := divide a b

definition modulo (a b : ℤ) : ℤ := a - a div b * b

notation a mod b := modulo a b

notation a = b [mod c] := a mod c = b mod c

/- div  -/

theorem of_nat_div_of_nat (m n : nat) : m div n = of_nat (#nat m div n) :=
nat.cases_on n
  (by rewrite [↑divide, sign_zero, zero_mul, nat.div_zero])
  (take n, by rewrite [↑divide, sign_of_succ, one_mul])

theorem neg_succ_of_nat_div (m : nat) {b : ℤ} (H : b > 0) :
  -[m +1] div b = -(m div b + 1) :=
calc
  -[m +1] div b = sign b * _              : rfl
     ... = -[(#nat m div (nat_abs b)) +1] : by rewrite [sign_of_pos H, one_mul]
     ... = -(m div b + 1)                 : by rewrite [↑divide, sign_of_pos H, one_mul]

theorem div_neg (a b : ℤ) : a div -b = -(a div b) :=
by rewrite [↑divide, sign_neg, neg_mul_eq_neg_mul, nat_abs_neg]

theorem div_of_neg_of_pos {a b : ℤ} (Ha : a < 0) (Hb : b > 0) : a div b = -((-a - 1) div b + 1) :=
obtain m (H1 : a = -[m +1]), from exists_eq_neg_succ_of_nat Ha,
calc
  a div b = -(m div b + 1)       : by rewrite [H1, neg_succ_of_nat_div _ Hb]
      ... = -((-a -1) div b + 1) : by rewrite [H1, neg_succ_of_nat_eq', neg_sub, sub_neg_eq_add,
                                               add.comm 1, add_sub_cancel]

theorem div_nonneg {a b : ℤ} (Ha : a ≥ 0) (Hb : b ≥ 0) : a div b ≥ 0 :=
obtain (m : ℕ) (Hm : a = m), from exists_eq_of_nat Ha,
obtain (n : ℕ) (Hn : b = n), from exists_eq_of_nat Hb,
calc
  a div b = (#nat m div n) : by rewrite [Hm, Hn, of_nat_div_of_nat]
      ... ≥ 0              : begin change (0 ≤ #nat m div n), apply trivial end

theorem div_nonpos {a b : ℤ} (Ha : a ≥ 0) (Hb : b ≤ 0) : a div b ≤ 0 :=
calc
  a div b = -(a div -b) : by rewrite [div_neg, neg_neg]
      ... ≤ 0           : neg_nonpos_of_nonneg (div_nonneg Ha (neg_nonneg_of_nonpos Hb))

theorem div_neg' {a b : ℤ} (Ha : a < 0) (Hb : b > 0) : a div b < 0 :=
have H1 : -a - 1 ≥ 0, from le_sub_one_of_lt (neg_pos_of_neg Ha),
have H2 : (-a - 1) div b + 1 > 0, from lt_add_one_of_le (div_nonneg H1 (le_of_lt Hb)),
calc
  a div b = -((-a - 1) div b + 1) : div_of_neg_of_pos Ha Hb
      ... < 0                     : neg_neg_of_pos H2

theorem zero_div (b : ℤ) : 0 div b = 0 :=
calc
  0 div b = sign b * (#nat 0 div (nat_abs b)) : rfl
      ... = sign b * 0 : nat.zero_div
      ... = 0          : mul_zero

theorem div_zero (a : ℤ) : a div 0 = 0 :=
by rewrite [↑divide, sign_zero, zero_mul]

theorem div_one (a : ℤ) :a div 1 = a :=
assert H : 1 > 0, from dec_trivial,
int.cases_on a
  (take m, by rewrite [of_nat_div_of_nat, nat.div_one])
  (take m, by rewrite [!neg_succ_of_nat_div H, of_nat_div_of_nat, nat.div_one])

theorem eq_div_mul_add_mod {a b : ℤ} : a = a div b * b + a mod b :=
!add.comm ▸ eq_add_of_sub_eq rfl

theorem div_eq_zero_of_lt {a b : ℤ} : 0 ≤ a → a < b → a div b = 0 :=
int.cases_on a
  (take m, assume H,
    int.cases_on b
      (take n,
        assume H : m < n,
        calc
          m div n = #nat m div n : of_nat_div_of_nat
              ... = 0            : nat.div_eq_zero_of_lt (lt_of_of_nat_lt_of_nat H))
      (take n,
        assume H : m < -[ n +1],
        have H1 : ¬(m < -[ n +1]), from dec_trivial,
        absurd H H1))
  (take m,
    assume H : 0 ≤ -[ m +1],
    have H1 : ¬ (0 ≤ -[ m +1]), from dec_trivial,
    absurd H H1)

theorem div_eq_zero_of_lt_abs {a b : ℤ} (H1 : 0 ≤ a) (H2 : a < abs b) : a div b = 0 :=
lt.by_cases
  (assume H : b < 0,
    assert H3 : a < -b, from abs_of_neg H ▸ H2,
    calc
      a div b = - (a div -b) : by rewrite [div_neg, neg_neg]
          ... = 0            : by rewrite [div_eq_zero_of_lt H1 H3, neg_zero])
  (assume H : b = 0, H⁻¹ ▸ !div_zero)
  (assume H : b > 0,
    have H3 : a < b, from abs_of_pos H ▸ H2,
    div_eq_zero_of_lt H1 H3)

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
              by rewrite [-*add.assoc, add.comm (-m), add.right_comm (-1), (add.comm b)]
    ... = b - 1 - m mod b                :
              by rewrite [↑modulo, *sub_eq_add_neg, neg_add, neg_neg]

theorem mod_neg (a b : ℤ) : a mod -b = a mod b :=
calc
  a mod -b = a - (a div -b) * -b : rfl
       ... = a - -(a div b) * -b : div_neg
       ... = a - a div b * b     : neg_mul_neg
       ... = a mod b             : rfl

theorem mod_abs (a b : ℤ) : a mod (abs b) = a mod b :=
abs.by_cases rfl !mod_neg

theorem zero_mod (b : ℤ) : 0 mod b = 0 :=
by rewrite [↑modulo, zero_div, zero_mul, sub_zero]

theorem mod_zero (a : ℤ) : a mod 0 = a :=
by rewrite [↑modulo, mul_zero, sub_zero]

theorem mod_one (a : ℤ) : a mod 1 = 0 :=
calc
  a mod 1 = a - a div 1 * 1 : rfl
      ... = 0 : by rewrite [mul_one, div_one, sub_self]

private lemma of_nat_mod_abs (m : ℕ) (b : ℤ) : m mod (abs b) = (#nat m mod (nat_abs b)) :=
calc
  m mod (abs b) = m mod (nat_abs b)        : of_nat_nat_abs
            ... = (#nat m mod (nat_abs b)) : of_nat_mod_of_nat

private lemma of_nat_mod_abs_lt (m : ℕ) {b : ℤ} (H : b ≠ 0) : m mod (abs b) < (abs b) :=
have H1 : abs b > 0, from abs_pos_of_ne_zero H,
have H2 : (#nat nat_abs b > 0), from lt_of_of_nat_lt_of_nat (!of_nat_nat_abs⁻¹ ▸ H1),
calc
  m mod (abs b) = (#nat m mod (nat_abs b)) : of_nat_mod_abs m b
        ... < nat_abs b : of_nat_lt_of_nat (nat.mod_lt H2)
        ... = abs b       : of_nat_nat_abs _

theorem mod_nonneg (a : ℤ) {b : ℤ} (H : b ≠ 0) : a mod b ≥ 0 :=
have H1 : abs b > 0, from abs_pos_of_ne_zero H,
have H2 : a mod (abs b) ≥ 0, from
  int.cases_on a
    (take m, (of_nat_mod_abs m b)⁻¹ ▸ !of_nat_nonneg)
    (take m,
      have H3 : 1 + m mod (abs b) ≤ (abs b),
        from (!add.comm ▸ add_one_le_of_lt (of_nat_mod_abs_lt m H)),
      calc
        -[ m +1] mod (abs b) = abs b - 1 - m mod (abs b) : neg_succ_of_nat_mod _ H1
          ... = abs b - (1 + m mod (abs b))    : by rewrite [*sub_eq_add_neg, neg_add, add.assoc]
          ... ≥ 0                              : iff.mp' !sub_nonneg_iff_le H3),
!mod_abs ▸ H2

theorem mod_lt (a : ℤ) {b : ℤ} (H : b ≠ 0) : a mod b < (abs b) :=
have H1 : abs b > 0, from abs_pos_of_ne_zero H,
have H2 : a mod (abs b) < abs b, from
  int.cases_on a
    (take m, of_nat_mod_abs_lt m H)
    (take m,
      have H3 : abs b ≠ 0, from assume H', H (eq_zero_of_abs_eq_zero H'),
      have H4 : 1 + m mod (abs b) > 0, from add_pos_of_pos_of_nonneg dec_trivial (mod_nonneg _ H3),
      calc
        -[ m +1] mod (abs b) = abs b - 1 - m mod (abs b) : neg_succ_of_nat_mod _ H1
          ... = abs b - (1 + m mod (abs b))      : by rewrite [*sub_eq_add_neg, neg_add, add.assoc]
          ... < abs b                            : sub_lt_self _ H4),
!mod_abs ▸ H2

/- both div and mod -/

private theorem add_mul_div_self_aux1 {a : ℤ} {k : ℕ} (n : ℕ)
    (H1 : a ≥ 0) (H2 : #nat k > 0) :
  (a + n * k) div k = a div k + n :=
obtain m (Hm : a = of_nat m), from exists_eq_of_nat H1,
Hm⁻¹ ▸ (calc
  (m + n * k) div k = (#nat (m + n * k)) div k : rfl
                ... = (#nat (m + n * k) div k) : of_nat_div_of_nat
                ... = (#nat m div k + n)       : !nat.add_mul_div_self H2
                ... = (#nat m div k) + n       : rfl
                ... = m div k + n : of_nat_div_of_nat)

private theorem add_mul_div_self_aux2 {a : ℤ} {k : ℕ} (n : ℕ)
    (H1 : a < 0) (H2 : #nat k > 0) :
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
                  by rewrite [add.comm, -sub_eq_add_neg, of_nat_add, of_nat_div_of_nat]
        ... = -[m +1] div k + n                         :
                  neg_succ_of_nat_div m (of_nat_lt_of_nat H2)))
  (assume nk_le_m : #nat n * k ≤ m,
    eq.symm (Hm⁻¹ ▸ (calc
      -[m +1] div k + n = -(m div k + 1) + n              :
                  neg_succ_of_nat_div m (of_nat_lt_of_nat H2)
        ... = -((#nat m div k) + 1) + n                   : of_nat_div_of_nat
        ... = -((#nat (m - n * k + n * k) div k) + 1) + n : nat.sub_add_cancel nk_le_m
        ... = -((#nat (m - n * k) div k + n) + 1) + n     : nat.add_mul_div_self H2
        ... = -((#nat m - n * k) div k + 1)               :
                   by rewrite [of_nat_add, *neg_add, add.right_comm, neg_add_cancel_right,
                               of_nat_div_of_nat]
        ... = -[(#nat m - n * k) +1] div k                :
                   neg_succ_of_nat_div _ (of_nat_lt_of_nat H2)
        ... = -((#nat m - n * k) + 1) div k               : rfl
        ... = -(m - (#nat n * k) + 1) div k               : of_nat_sub_of_nat nk_le_m
        ... = (-(m + 1) + n * k) div k                    :
                   by rewrite [sub_eq_add_neg, -*add.assoc, *neg_add, neg_neg, add.right_comm]
        ... = (-[m +1] + n * k) div k                     : rfl)))

private theorem add_mul_div_self_aux3 (a : ℤ) {b c : ℤ} (H1 : b ≥ 0) (H2 : c > 0) :
    (a + b * c) div c = a div c + b :=
obtain n (Hn : b = of_nat n), from exists_eq_of_nat H1,
obtain k (Hk : c = of_nat k), from exists_eq_of_nat (le_of_lt H2),
have knz : k ≠ 0, from assume kz, !lt.irrefl (kz ▸ Hk ▸ H2),
have kgt0 : (#nat k > 0), from nat.pos_of_ne_zero knz,
have H3 : (a + n * k) div k = a div k + n, from
  or.elim (lt_or_ge a 0)
    (assume Ha : a < 0, add_mul_div_self_aux2 _ Ha kgt0)
    (assume Ha : a ≥ 0, add_mul_div_self_aux1 _ Ha kgt0),
Hn⁻¹ ▸ Hk⁻¹ ▸ H3

private theorem add_mul_div_self_aux4 (a b : ℤ) {c : ℤ} (H : c > 0) :
    (a + b * c) div c = a div c + b :=
or.elim (le.total 0 b)
  (assume H1 : 0 ≤ b, add_mul_div_self_aux3 _ H1 H)
  (assume H1 : 0 ≥ b,
    eq.symm (calc
      a div c + b = (a + b * c + -b * c) div c + b :
                        by rewrite [-neg_mul_eq_neg_mul, add_neg_cancel_right]
              ... = (a + b * c) div c + - b + b :
                        add_mul_div_self_aux3 _ (neg_nonneg_of_nonpos H1) H
              ... = (a + b * c) div c : neg_add_cancel_right))

theorem add_mul_div_self (a b : ℤ) {c : ℤ} (H : c ≠ 0) : (a + b * c) div c = a div c + b :=
lt.by_cases
  (assume H1 : 0 < c, !add_mul_div_self_aux4 H1)
  (assume H1 : 0 = c, absurd H1⁻¹ H)
  (assume H1 : 0 > c,
    have H2 : -c > 0, from neg_pos_of_neg H1,
    calc
      (a + b * c) div c = - ((a + -b * -c) div -c) : by rewrite [div_neg, neg_mul_neg, neg_neg]
                    ... = -(a div -c + -b)         : !add_mul_div_self_aux4 H2
                    ... = a div c + b              : by rewrite [div_neg, neg_add, *neg_neg])

theorem add_mul_div_self_left (a : ℤ) {b : ℤ} (c : ℤ) (H : b ≠ 0) :
    (a + b * c) div b = a div b + c :=
!mul.comm ▸ !add_mul_div_self H

theorem mul_div_cancel (a : ℤ) {b : ℤ} (H : b ≠ 0) : a * b div b = a :=
calc
  a * b div b = (0 + a * b) div b : zero_add
          ... = 0 div b + a       : !add_mul_div_self H
          ... = a                 : by rewrite [zero_div, zero_add]

theorem mul_div_cancel_left {a : ℤ} (b : ℤ) (H : a ≠ 0) : a * b div a = b :=
!mul.comm ▸ mul_div_cancel b H

theorem div_self {a : ℤ} (H : a ≠ 0) : a div a = 1 :=
!mul_one ▸ !mul_div_cancel_left H

theorem mod_self {a : ℤ} : a mod a = 0 :=
decidable.by_cases
  (assume H : a = 0, H⁻¹ ▸ !mod_zero)
  (assume H : a ≠ 0,
    calc
      a mod a = a - a div a * a : rfl
          ... = 0 : by rewrite [!div_self H, one_mul, sub_self])

theorem mod_lt_of_pos (a : ℤ) {b : ℤ} (H : b > 0) : a mod b < b :=
!abs_of_pos H ▸ !mod_lt (ne.symm (ne_of_lt H))

theorem mul_div_mul_of_pos_aux {a : ℤ} (b : ℤ) {c : ℤ}
  (H1 : a > 0) (H2 : c > 0) : a * b div (a * c) = b div c :=
have H3 : a * c ≠ 0, from ne.symm (ne_of_lt (mul_pos H1 H2)),
have H4 : a * (b mod c) < a * c, from mul_lt_mul_of_pos_left (!mod_lt_of_pos H2)  H1,
have H5 : a * (b mod c) ≥ 0, from mul_nonneg (le_of_lt H1) (!mod_nonneg (ne.symm (ne_of_lt H2))),
calc
  a * b div (a * c) = a * (b div c * c + b mod c) div (a * c) : eq_div_mul_add_mod

    ... = (a * (b mod c) + a * c * (b div c)) div (a * c)     :
              by rewrite [!add.comm, mul.left_distrib, mul.comm _ c, -!mul.assoc]
    ... = a * (b mod c) div (a * c) + b div c                 : !add_mul_div_self_left H3
    ... = 0 + b div c                                         : {!div_eq_zero_of_lt H5 H4}
    ... = b div c                                             : zero_add

theorem mul_div_mul_of_pos {a : ℤ} (b c : ℤ) (H : a > 0) : a * b div (a * c) = b div c :=
lt.by_cases
  (assume H1 : c < 0,
    have H2 : -c > 0, from neg_pos_of_neg H1,
    calc
      a * b div (a * c) = - (a * b div (a * -c)) :
                              by rewrite [!neg_mul_eq_mul_neg⁻¹, div_neg, neg_neg]
                    ... = - (b div -c)           : mul_div_mul_of_pos_aux _ H H2
                    ... = b div c : by rewrite [div_neg, neg_neg])
  (assume H1 : c = 0,
    calc
      a * b div (a * c) = 0       : by rewrite [H1, mul_zero, div_zero]
                    ... = b div c : by rewrite [H1, div_zero])
  (assume H1 : c > 0,
    mul_div_mul_of_pos_aux _ H H1)

theorem mul_div_mul_of_pos_left (a : ℤ) {b : ℤ} (c : ℤ) (H : b > 0) : a * b div (c * b) = a div c :=
!mul.comm ▸ !mul.comm ▸ !mul_div_mul_of_pos H

theorem div_mul_le (a : ℤ) {b : ℤ} (H : b ≠ 0) : a div b * b ≤ a :=
calc
  a = a div b * b + a mod b : eq_div_mul_add_mod
    ... ≥ a div b * b       : le_add_of_nonneg_right (!mod_nonneg H)

theorem lt_div_add_one_mul_self (a : ℤ) {b : ℤ} (H : b > 0) : a < (a div b + 1) * b :=
have H : a - a div b * b < b, from !mod_lt_of_pos H,
calc
      a < a div b * b + b    : iff.mp' !lt_add_iff_sub_lt_left H
    ... = (a div b + 1) * b  : by rewrite [mul.right_distrib, one_mul]

theorem div_le_of_nonneg_of_nonneg {a b : ℤ} (Ha : a ≥ 0) (Hb : b ≥ 0) : a div b ≤ a :=
obtain (m : ℕ) (Hm : a = m), from exists_eq_of_nat Ha,
obtain (n : ℕ) (Hn : b = n), from exists_eq_of_nat Hb,
calc
  a div b = #nat m div n : by rewrite [Hm, Hn, of_nat_div_of_nat]
     ... ≤ m             : of_nat_le_of_nat !nat.div_le
     ... = a             : Hm

theorem abs_div_le_abs (a b : ℤ) : abs (a div b) ≤ abs a :=
have H : ∀a b, b > 0 → abs (a div b) ≤ abs a, from
  take a b,
  assume H1 : b > 0,
  or.elim (le_or_gt 0 a)
    (assume H2 : 0 ≤ a,
      have H3 : 0 ≤ b, from le_of_lt H1,
      calc
        abs (a div b) = a div b : abs_of_nonneg (div_nonneg H2 H3)
                  ... ≤ a       : div_le_of_nonneg_of_nonneg H2 H3
                  ... = abs a   : abs_of_nonneg H2)
    (assume H2 : a < 0,
      have H3 : -a - 1 ≥ 0, from le_sub_one_of_lt (neg_pos_of_neg H2),
      have H4 : (-a - 1) div b + 1 ≥ 0, from add_nonneg (div_nonneg H3 (le_of_lt H1)) (of_nat_le_of_nat !nat.zero_le),
      have H5 : (-a - 1) div b ≤ -a - 1, from div_le_of_nonneg_of_nonneg H3 (le_of_lt H1),
      calc
        abs (a div b) = abs ((-a - 1) div b + 1) : by rewrite [div_of_neg_of_pos H2 H1, abs_neg]
                  ... = (-a - 1) div b + 1       : abs_of_nonneg H4
                  ... ≤ -a - 1 + 1               : add_le_add_right H5 _
                  ... = abs a                    : by rewrite [sub_add_cancel, abs_of_neg H2]),
lt.by_cases
  (assume H1 : b < 0,
    calc
      abs (a div b) = abs (a div -b) : by rewrite [div_neg, abs_neg]
                ... ≤ abs a          : H _ _ (neg_pos_of_neg H1))
  (assume H1 : b = 0,
    calc
      abs (a div b) = 0 : by rewrite [H1, div_zero, abs_zero]
                ... ≤ abs a : abs_nonneg)
  (assume H1 : b > 0, H _ _ H1)

/- ltz_divLR -/

end int
