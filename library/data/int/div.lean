/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

Definitions and properties of div and mod, following the SSReflect library.

Following SSReflect and the SMTlib standard, we define a % b so that 0 ≤ a % b < |b| when b ≠ 0.
-/
import data.int.order data.nat.div
open [coercions] [reduce_hints] nat
open [declarations] [classes] nat (succ)
open algebra
open eq.ops

namespace int

/- definitions -/

protected definition div (a b : ℤ) : ℤ :=
sign b *
  (match a with
    | of_nat m := of_nat (m / (nat_abs b))
    | -[1+m]   := -[1+ ((m:nat) / (nat_abs b))]
  end)

definition int_has_div [reducible] [instance] [priority int.prio] : has_div int :=
has_div.mk int.div

lemma of_nat_div_eq (m : nat) (b : ℤ) : (of_nat m) / b = sign b * of_nat (m / (nat_abs b)) :=
rfl

lemma neg_succ_div_eq (m: nat) (b : ℤ) : -[1+m] / b = sign b * -[1+ (m / (nat_abs b))] :=
rfl

lemma div_def (a b : ℤ) : a / b =
  sign b *
    (match a with
      | of_nat m := of_nat (m / (nat_abs b))
      | -[1+m]   := -[1+ ((m:nat) / (nat_abs b))]
    end) :=
rfl

protected definition mod (a b : ℤ) : ℤ := a - a / b * b

definition int_has_mod [reducible] [instance] [priority int.prio] : has_mod int :=
has_mod.mk int.mod


lemma mod_def (a b : ℤ) : a % b = a - a / b * b :=
rfl

notation [priority int.prio] a ≡ b `[mod `:0 c:0 `]` := a % c = b % c

/- /  -/

theorem of_nat_div (m n : nat) : of_nat (m / n) = (of_nat m) / (of_nat n) :=
nat.cases_on n
  (begin rewrite [of_nat_div_eq, of_nat_zero, sign_zero, zero_mul, nat.div_zero] end)
  (take (n : nat), by rewrite [of_nat_div_eq, sign_of_succ, one_mul])

theorem neg_succ_of_nat_div (m : nat) {b : ℤ} (H : b > 0) :
  -[1+m] / b = -(m / b + 1) :=
calc
  -[1+m] / b = sign b * _         : rfl
     ... = -[1+(m / (nat_abs b))] : by rewrite [sign_of_pos H, one_mul]
     ... = -(m / b + 1)           : by rewrite [of_nat_div_eq, sign_of_pos H, one_mul]

protected theorem div_neg (a b : ℤ) : a / -b = -(a / b) :=
begin
  induction a,
    rewrite [*of_nat_div_eq, sign_neg, neg_mul_eq_neg_mul, nat_abs_neg],
    rewrite [*neg_succ_div_eq, sign_neg, neg_mul_eq_neg_mul, nat_abs_neg],
end

theorem div_of_neg_of_pos {a b : ℤ} (Ha : a < 0) (Hb : b > 0) : a / b = -((-a - 1) / b + 1) :=
obtain (m : nat) (H1 : a = -[1+m]), from exists_eq_neg_succ_of_nat Ha,
calc
  a / b = -(m / b + 1)         : by rewrite [H1, neg_succ_of_nat_div _ Hb]
      ... = -((-a -1) / b + 1) : by rewrite [H1, neg_succ_of_nat_eq', neg_sub, sub_neg_eq_add,
                                               add.comm 1, add_sub_cancel]

protected theorem div_nonneg {a b : ℤ} (Ha : a ≥ 0) (Hb : b ≥ 0) : a / b ≥ 0 :=
obtain (m : ℕ) (Hm : a = m), from exists_eq_of_nat Ha,
obtain (n : ℕ) (Hn : b = n), from exists_eq_of_nat Hb,
calc
  a / b = m / n : by rewrite [Hm, Hn]
      ... ≥ 0       : by rewrite -of_nat_div; apply trivial

protected theorem div_nonpos {a b : ℤ} (Ha : a ≥ 0) (Hb : b ≤ 0) : a / b ≤ 0 :=
calc
  a / b = -(a / -b) : by rewrite [int.div_neg, neg_neg]
      ... ≤ 0       : neg_nonpos_of_nonneg (int.div_nonneg Ha (neg_nonneg_of_nonpos Hb))

theorem div_neg' {a b : ℤ} (Ha : a < 0) (Hb : b > 0) : a / b < 0 :=
have -a - 1 ≥ 0, from le_sub_one_of_lt (neg_pos_of_neg Ha),
have (-a - 1) / b + 1 > 0, from lt_add_one_of_le (int.div_nonneg this (le_of_lt Hb)),
calc
  a / b = -((-a - 1) / b + 1) : div_of_neg_of_pos Ha Hb
      ... < 0                 : neg_neg_of_pos this

protected theorem zero_div (b : ℤ) : 0 / b = 0 :=
by rewrite [of_nat_div_eq, nat.zero_div, of_nat_zero, mul_zero]

protected theorem div_zero (a : ℤ) : a / 0 = 0 :=
by rewrite [div_def, sign_zero, zero_mul]

protected theorem div_one (a : ℤ) : a / 1 = a :=
assert (1 : int) > 0, from dec_trivial,
int.cases_on a
  (take m : nat, by rewrite [-of_nat_one, -of_nat_div, nat.div_one])
  (take m : nat, by rewrite [!neg_succ_of_nat_div this, -of_nat_one, -of_nat_div, nat.div_one])

theorem eq_div_mul_add_mod (a b : ℤ) : a = a / b * b + a % b :=
!add.comm ▸ eq_add_of_sub_eq rfl

theorem div_eq_zero_of_lt {a b : ℤ} : 0 ≤ a → a < b → a / b = 0 :=
int.cases_on a
  (take (m : nat), assume H,
    int.cases_on b
      (take (n : nat),
        assume H : m < n,
        show m / n = 0,
          by rewrite [-of_nat_div, nat.div_eq_zero_of_lt (lt_of_of_nat_lt_of_nat H)])
      (take (n : nat),
        assume H : m < -[1+n],
        have H1 : ¬(m < -[1+n]), from dec_trivial,
        absurd H H1))
  (take (m : nat),
    assume H : 0 ≤ -[1+m],
    have ¬ (0 ≤ -[1+m]), from dec_trivial,
    absurd H this)

theorem div_eq_zero_of_lt_abs {a b : ℤ} (H1 : 0 ≤ a) (H2 : a < abs b) : a / b = 0 :=
lt.by_cases
  (suppose b < 0,
    assert a < -b, from abs_of_neg this ▸ H2,
    calc
      a / b = - (a / -b) : by rewrite [int.div_neg, neg_neg]
          ... = 0         : by rewrite [div_eq_zero_of_lt H1 this, neg_zero])
  (suppose b = 0, this⁻¹ ▸ !int.div_zero)
  (suppose b > 0,
    have a < b, from abs_of_pos this ▸ H2,
    div_eq_zero_of_lt H1 this)

private theorem add_mul_div_self_aux1 {a : ℤ} {k : ℕ} (n : ℕ) (H1 : a ≥ 0) (H2 : k > 0) :
  (a + n * k) / k = a / k + n :=
obtain (m : nat) (Hm : a = of_nat m), from exists_eq_of_nat H1,
begin
  subst Hm,
  rewrite [-of_nat_mul, -of_nat_add, -*of_nat_div, -of_nat_add, !nat.add_mul_div_self H2]
end

private theorem add_mul_div_self_aux2 {a : ℤ} {k : ℕ} (n : ℕ) (H1 : a < 0) (H2 : k > 0) :
  (a + n * k) / k = a / k + n :=
obtain m (Hm : a = -[1+m]), from exists_eq_neg_succ_of_nat H1,
or.elim (nat.lt_or_ge m (n * k))
  (assume m_lt_nk : m < n * k,
    assert H3 : m + 1 ≤ n * k, from nat.succ_le_of_lt m_lt_nk,
    assert H4 : m / k + 1 ≤ n,
      from nat.succ_le_of_lt (nat.div_lt_of_lt_mul m_lt_nk),
    have (-[1+m] + n * k) / k = -[1+m] / k + n, from calc
      (-[1+m] + n * k) / k
            = of_nat ((k * n - (m + 1)) / k) :
                by rewrite [add.comm, neg_succ_of_nat_eq, of_nat_div, algebra.mul.comm k n,
                            of_nat_sub H3]
        ... = of_nat (n - m / k - 1)         :
                nat.mul_sub_div_of_lt (!nat.mul_comm ▸ m_lt_nk)
        ... = -[1+m] / k + n                 :
                by rewrite [nat.sub_sub, of_nat_sub H4, int.add_comm, sub_eq_add_neg,
                            !neg_succ_of_nat_div (of_nat_lt_of_nat_of_lt H2),
                            of_nat_add, of_nat_div],
    Hm⁻¹ ▸ this)
  (assume nk_le_m :  n * k ≤ m,
    have -[1+m] / k + n = (-[1+m] + n * k) / k, from calc
      -[1+m] / k + n
            = -(of_nat ((m - n * k + n * k) / k) + 1) + n :
                by rewrite [neg_succ_of_nat_div m (of_nat_lt_of_nat_of_lt H2),
                            nat.sub_add_cancel nk_le_m, of_nat_div]
        ... = -(of_nat ((m - n * k) / k + n) + 1) + n     : nat.add_mul_div_self H2
        ... = -(of_nat (m - n * k) / k + 1)               :
                   by rewrite [of_nat_add, *neg_add, add.right_comm, neg_add_cancel_right,
                               of_nat_div]
        ... = -[1+(m - n * k)] / k                        :
                   neg_succ_of_nat_div _ (of_nat_lt_of_nat_of_lt H2)
        ... = -(of_nat(m - n * k) + 1) / k                : rfl
        ... = -(of_nat m - of_nat(n * k) + 1) / k         : of_nat_sub nk_le_m
        ... = (-(of_nat m + 1) + n * k) / k               :
                   by rewrite [sub_eq_add_neg, -*add.assoc, *neg_add, neg_neg, add.right_comm]
        ... = (-[1+m] + n * k) / k                        : rfl,
    Hm⁻¹ ▸ this⁻¹)

private theorem add_mul_div_self_aux3 (a : ℤ) {b c : ℤ} (H1 : b ≥ 0) (H2 : c > 0) :
    (a + b * c) / c = a / c + b :=
obtain (n : nat) (Hn : b = of_nat n), from exists_eq_of_nat H1,
obtain (k : nat) (Hk : c = of_nat k), from exists_eq_of_nat (le_of_lt H2),
have knz : k ≠ 0, from assume kz, !lt.irrefl (kz ▸ Hk ▸ H2),
have kgt0 : (#nat k > 0), from nat.pos_of_ne_zero knz,
have H3 : (a + n * k) / k = a / k + n, from
  or.elim (lt_or_ge a 0)
    (assume Ha : a < 0, add_mul_div_self_aux2 _ Ha kgt0)
    (assume Ha : a ≥ 0, add_mul_div_self_aux1 _ Ha kgt0),
Hn⁻¹ ▸ Hk⁻¹ ▸ H3

private theorem add_mul_div_self_aux4 (a b : ℤ) {c : ℤ} (H : c > 0) :
    (a + b * c) / c = a / c + b :=
or.elim (le.total 0 b)
  (assume H1 : 0 ≤ b, add_mul_div_self_aux3 _ H1 H)
  (assume H1 : 0 ≥ b,
    eq.symm (calc
      a / c + b = (a + b * c + -b * c) / c + b :
                        by rewrite [-neg_mul_eq_neg_mul, add_neg_cancel_right]
              ... = (a + b * c) / c + - b + b  :
                        add_mul_div_self_aux3 _ (neg_nonneg_of_nonpos H1) H
              ... = (a + b * c) / c            : neg_add_cancel_right))

protected theorem add_mul_div_self (a b : ℤ) {c : ℤ} (H : c ≠ 0) :
  (a + b * c) / c = a / c + b :=
lt.by_cases
  (assume H1 : 0 < c, !add_mul_div_self_aux4 H1)
  (assume H1 : 0 = c, absurd H1⁻¹ H)
  (assume H1 : 0 > c,
    have H2 : -c > 0, from neg_pos_of_neg H1,
    calc
      (a + b * c) / c = - ((a + -b * -c) / -c) : by rewrite [int.div_neg, neg_mul_neg, neg_neg]
                    ... = -(a / -c + -b)       : !add_mul_div_self_aux4 H2
                    ... = a / c + b            : by rewrite [int.div_neg, neg_add, *neg_neg])

protected theorem add_mul_div_self_left (a : ℤ) {b : ℤ} (c : ℤ) (H : b ≠ 0) :
    (a + b * c) / b = a / b + c :=
!mul.comm ▸ !int.add_mul_div_self H

protected theorem mul_div_cancel (a : ℤ) {b : ℤ} (H : b ≠ 0) : a * b / b = a :=
calc
  a * b / b = (0 + a * b) / b : zero_add
          ... = 0 / b + a     : !int.add_mul_div_self H
          ... = a             : by rewrite [int.zero_div, zero_add]

protected theorem mul_div_cancel_left {a : ℤ} (b : ℤ) (H : a ≠ 0) : a * b / a = b :=
!mul.comm ▸ int.mul_div_cancel b H

protected theorem div_self {a : ℤ} (H : a ≠ 0) : a / a = 1 :=
!mul_one ▸ !int.mul_div_cancel_left H

/- mod -/

theorem of_nat_mod (m n : nat) : m % n = of_nat (m % n) :=
have H : m = of_nat (m % n) + m / n * n, from calc
  m = of_nat (m / n * n + m % n)              : nat.eq_div_mul_add_mod
    ... = of_nat (m / n) * n + of_nat (m % n) : rfl
    ... = m / n * n + of_nat (m % n)          : of_nat_div
    ... = of_nat (m % n) + m / n * n          : add.comm,
calc
  m % n = m - m / n * n : rfl
      ... = of_nat (m % n)  : sub_eq_of_eq_add H

theorem neg_succ_of_nat_mod (m : ℕ) {b : ℤ} (bpos : b > 0) :
  -[1+m] % b = b - 1 - m % b :=
calc
  -[1+m] % b = -(m + 1) - -[1+m] / b * b : rfl
    ... = -(m + 1) - -(m / b + 1) * b    : neg_succ_of_nat_div _ bpos
    ... = -m + -1 + (b + m / b * b)      :
              by rewrite [neg_add, -neg_mul_eq_neg_mul, sub_neg_eq_add, right_distrib,
                                 one_mul, (add.comm b)]
    ... = b + -1 + (-m + m / b * b)      :
              by rewrite [-*add.assoc, add.comm (-m), add.right_comm (-1), (add.comm b)]
    ... = b - 1 - m % b                  :
              by rewrite [(mod_def), *sub_eq_add_neg, neg_add, neg_neg]
                -- it seems the parser has difficulty here, because "mod" is a token?

theorem mod_neg (a b : ℤ) : a % -b = a % b :=
calc
  a % -b = a - (a / -b) * -b   : rfl
       ... = a - -(a / b) * -b : int.div_neg
       ... = a - a / b * b     : neg_mul_neg
       ... = a % b             : rfl

theorem mod_abs (a b : ℤ) : a % (abs b) = a % b :=
abs.by_cases rfl !mod_neg

theorem zero_mod (b : ℤ) : 0 % b = 0 :=
by rewrite [(mod_def), int.zero_div, zero_mul, sub_zero]

theorem mod_zero (a : ℤ) : a % 0 = a :=
by rewrite [(mod_def), mul_zero, sub_zero]

theorem mod_one (a : ℤ) : a % 1 = 0 :=
calc
  a % 1 = a - a / 1 * 1 : rfl
      ... = 0 : by rewrite [mul_one, int.div_one, sub_self]

private lemma of_nat_mod_abs (m : ℕ) (b : ℤ) : m % (abs b) = of_nat (m % (nat_abs b)) :=
calc
  m % (abs b) = m % (nat_abs b)            : of_nat_nat_abs
            ... = of_nat (m % (nat_abs b)) : of_nat_mod

private lemma of_nat_mod_abs_lt (m : ℕ) {b : ℤ} (H : b ≠ 0) : m % (abs b) < (abs b) :=
have H1 : abs b > 0, from abs_pos_of_ne_zero H,
have H2 : (#nat nat_abs b > 0), from lt_of_of_nat_lt_of_nat (!of_nat_nat_abs⁻¹ ▸ H1),
calc
  m % (abs b) = of_nat (m % (nat_abs b)) : of_nat_mod_abs m b
        ... < nat_abs b : of_nat_lt_of_nat_of_lt (!nat.mod_lt H2)
        ... = abs b       : of_nat_nat_abs _

theorem mod_eq_of_lt {a b : ℤ} (H1 : 0 ≤ a) (H2 : a < b) : a % b = a :=
obtain (m : nat) (Hm : a = of_nat m), from exists_eq_of_nat H1,
obtain (n : nat) (Hn : b = of_nat n), from exists_eq_of_nat (le_of_lt (lt_of_le_of_lt H1 H2)),
begin
  revert H2,
  rewrite [Hm, Hn, of_nat_mod, of_nat_lt_of_nat_iff, of_nat_eq_of_nat_iff],
  apply nat.mod_eq_of_lt
end

theorem mod_nonneg (a : ℤ) {b : ℤ} (H : b ≠ 0) : a % b ≥ 0 :=
have H1 : abs b > 0, from abs_pos_of_ne_zero H,
have H2 : a % (abs b) ≥ 0, from
  int.cases_on a
    (take m : nat, (of_nat_mod_abs m b)⁻¹ ▸ of_nat_nonneg (nat.mod m (nat_abs b)))
    (take m : nat,
      have H3 : 1 + m % (abs b) ≤ (abs b),
        from (!add.comm ▸ add_one_le_of_lt (of_nat_mod_abs_lt m H)),
      calc
        -[1+m] % (abs b) = abs b - 1 - m % (abs b) : neg_succ_of_nat_mod _ H1
          ... = abs b - (1 + m % (abs b))          : by rewrite [*sub_eq_add_neg, neg_add, add.assoc]
          ... ≥ 0                                  : iff.mpr !sub_nonneg_iff_le H3),
!mod_abs ▸ H2

theorem mod_lt (a : ℤ) {b : ℤ} (H : b ≠ 0) : a % b < (abs b) :=
have H1 : abs b > 0, from abs_pos_of_ne_zero H,
have H2 : a % (abs b) < abs b, from
  int.cases_on a
    (take m, of_nat_mod_abs_lt m H)
    (take m : nat,
      have H3 : abs b ≠ 0, from assume H', H (eq_zero_of_abs_eq_zero H'),
      have H4 : 1 + m % (abs b) > 0,
        from add_pos_of_pos_of_nonneg dec_trivial (mod_nonneg _ H3),
      calc
        -[1+m] % (abs b) = abs b - 1 - m % (abs b) : neg_succ_of_nat_mod _ H1
          ... = abs b - (1 + m % (abs b))        : by rewrite [*sub_eq_add_neg, neg_add, add.assoc]
          ... < abs b                            : sub_lt_self _ H4),
!mod_abs ▸ H2

theorem add_mul_mod_self {a b c : ℤ} : (a + b * c) % c = a % c :=
decidable.by_cases
  (assume cz : c = 0, by rewrite [cz, mul_zero, add_zero])
  (assume cnz, by rewrite [(mod_def), !int.add_mul_div_self cnz, right_distrib,
                            sub_add_eq_sub_sub_swap, add_sub_cancel])

theorem add_mul_mod_self_left (a b c : ℤ) : (a + b * c) % b = a % b :=
!mul.comm ▸ !add_mul_mod_self

theorem add_mod_self {a b : ℤ} : (a + b) % b = a % b :=
by rewrite -(int.mul_one b) at {1}; apply add_mul_mod_self_left

theorem add_mod_self_left {a b : ℤ} : (a + b) % a = b % a :=
!add.comm ▸ !add_mod_self

theorem mod_add_mod (m n k : ℤ) : (m % n + k) % n = (m + k) % n :=
by rewrite [eq_div_mul_add_mod m n at {2}, add.assoc, add.comm (m / n * n), add_mul_mod_self]

theorem add_mod_mod (m n k : ℤ) : (m + n % k) % k = (m + n) % k :=
by rewrite [add.comm, mod_add_mod, add.comm]

theorem add_mod_eq_add_mod_right {m n k : ℤ} (i : ℤ) (H : m % n = k % n) :
  (m + i) % n = (k + i) % n :=
by rewrite [-mod_add_mod, -mod_add_mod k, H]

theorem add_mod_eq_add_mod_left {m n k : ℤ} (i : ℤ) (H : m % n = k % n) :
  (i + m) % n = (i + k) % n :=
by rewrite [add.comm, add_mod_eq_add_mod_right _ H, add.comm]

theorem mod_eq_mod_of_add_mod_eq_add_mod_right {m n k i : ℤ}
    (H : (m + i) % n = (k + i) % n) :
  m % n = k % n :=
assert H1 : (m + i + (-i)) % n = (k + i + (-i)) % n, from add_mod_eq_add_mod_right _ H,
by rewrite [*add_neg_cancel_right at H1]; apply H1

theorem mod_eq_mod_of_add_mod_eq_add_mod_left {m n k i : ℤ} :
  (i + m) % n = (i + k) % n → m % n = k % n :=
by rewrite [add.comm i m, add.comm i k]; apply mod_eq_mod_of_add_mod_eq_add_mod_right

theorem mul_mod_left (a b : ℤ) : (a * b) % b = 0 :=
by rewrite [-zero_add (a * b), add_mul_mod_self, zero_mod]

theorem mul_mod_right (a b : ℤ) : (a * b) % a = 0 :=
!mul.comm ▸ !mul_mod_left

theorem mod_self {a : ℤ} : a % a = 0 :=
decidable.by_cases
  (assume H : a = 0, H⁻¹ ▸ !mod_zero)
  (assume H : a ≠ 0,
    calc
      a % a = a - a / a * a : rfl
          ... = 0 : by rewrite [!int.div_self H, one_mul, sub_self])

theorem mod_lt_of_pos (a : ℤ) {b : ℤ} (H : b > 0) : a % b < b :=
!abs_of_pos H ▸ !mod_lt (ne.symm (ne_of_lt H))

/- properties of / and % -/

theorem mul_div_mul_of_pos_aux {a : ℤ} (b : ℤ) {c : ℤ}
  (H1 : a > 0) (H2 : c > 0) : a * b / (a * c) = b / c :=
have H3 : a * c ≠ 0, from ne.symm (ne_of_lt (mul_pos H1 H2)),
have H4 : a * (b % c) < a * c, from mul_lt_mul_of_pos_left (!mod_lt_of_pos H2)  H1,
have H5 : a * (b % c) ≥ 0, from mul_nonneg (le_of_lt H1) (!mod_nonneg (ne.symm (ne_of_lt H2))),
calc
  a * b / (a * c) = a * (b / c * c + b % c) / (a * c) : eq_div_mul_add_mod

    ... = (a * (b % c) + a * c * (b / c)) / (a * c)   :
              by rewrite [!add.comm, int.left_distrib, mul.comm _ c, -!mul.assoc]
    ... = a * (b % c) / (a * c) + b / c               : !int.add_mul_div_self_left H3
    ... = 0 + b / c                                   : {!div_eq_zero_of_lt H5 H4}
    ... = b / c                                       : zero_add

theorem mul_div_mul_of_pos {a : ℤ} (b c : ℤ) (H : a > 0) : a * b / (a * c) = b / c :=
lt.by_cases
  (assume H1 : c < 0,
    have H2 : -c > 0, from neg_pos_of_neg H1,
    calc
      a * b / (a * c) = - (a * b / (a * -c)) :
                              by rewrite [-neg_mul_eq_mul_neg, int.div_neg, neg_neg]
                    ... = - (b / -c)         : mul_div_mul_of_pos_aux _ H H2
                    ... = b / c : by rewrite [int.div_neg, neg_neg])
  (assume H1 : c = 0,
    calc
      a * b / (a * c) = 0       : by rewrite [H1, mul_zero, int.div_zero]
                    ... = b / c : by rewrite [H1, int.div_zero])
  (assume H1 : c > 0,
    mul_div_mul_of_pos_aux _ H H1)

theorem mul_div_mul_of_pos_left (a : ℤ) {b : ℤ} (c : ℤ) (H : b > 0) :
  a * b / (c * b) = a / c :=
!mul.comm ▸ !mul.comm ▸ !mul_div_mul_of_pos H

theorem mul_mod_mul_of_pos {a : ℤ} (b c : ℤ) (H : a > 0) : a * b % (a * c) = a * (b % c) :=
by rewrite [(mod_def), mod_def, !mul_div_mul_of_pos H, mul_sub_left_distrib, mul.left_comm]

theorem lt_div_add_one_mul_self (a : ℤ) {b : ℤ} (H : b > 0) : a < (a / b + 1) * b :=
have H : a - a / b * b < b, from !mod_lt_of_pos H,
calc
      a < a / b * b + b    : iff.mpr !lt_add_iff_sub_lt_left H
    ... = (a / b + 1) * b  : by rewrite [right_distrib, one_mul]

theorem div_le_of_nonneg_of_nonneg {a b : ℤ} (Ha : a ≥ 0) (Hb : b ≥ 0) : a / b ≤ a :=
obtain (m : ℕ) (Hm : a = m), from exists_eq_of_nat Ha,
obtain (n : ℕ) (Hn : b = n), from exists_eq_of_nat Hb,
calc
  a / b = of_nat (m / n) : by rewrite [Hm, Hn, of_nat_div]
     ... ≤ m             : of_nat_le_of_nat_of_le !nat.div_le_self
     ... = a             : Hm

theorem abs_div_le_abs (a b : ℤ) : abs (a / b) ≤ abs a :=
have H : ∀a b, b > 0 → abs (a / b) ≤ abs a, from
  take a b,
  assume H1 : b > 0,
  or.elim (le_or_gt 0 a)
    (assume H2 : 0 ≤ a,
      have H3 : 0 ≤ b, from le_of_lt H1,
      calc
        abs (a / b) = a / b   : abs_of_nonneg (int.div_nonneg H2 H3)
                  ... ≤ a     : div_le_of_nonneg_of_nonneg H2 H3
                  ... = abs a : abs_of_nonneg H2)
    (assume H2 : a < 0,
      have H3 : -a - 1 ≥ 0, from le_sub_one_of_lt (neg_pos_of_neg H2),
      have H4 : (-a - 1) / b + 1 ≥ 0,
        from add_nonneg (int.div_nonneg H3 (le_of_lt H1)) (of_nat_le_of_nat_of_le !nat.zero_le),
      have H5 : (-a - 1) / b ≤ -a - 1, from div_le_of_nonneg_of_nonneg H3 (le_of_lt H1),
      calc
        abs (a / b) = abs ((-a - 1) / b + 1) : by rewrite [div_of_neg_of_pos H2 H1, abs_neg]
                  ... = (-a - 1) / b + 1     : abs_of_nonneg H4
                  ... ≤ -a - 1 + 1           : add_le_add_right H5 _
                  ... = abs a                : by rewrite [sub_add_cancel, abs_of_neg H2]),
lt.by_cases
  (assume H1 : b < 0,
    calc
      abs (a / b) = abs (a / -b) : by rewrite [int.div_neg, abs_neg]
                ... ≤ abs a      : H _ _ (neg_pos_of_neg H1))
  (assume H1 : b = 0,
    calc
      abs (a / b) = 0 : by rewrite [H1, int.div_zero, abs_zero]
                ... ≤ abs a : abs_nonneg)
  (assume H1 : b > 0, H _ _ H1)

theorem div_mul_cancel_of_mod_eq_zero {a b : ℤ} (H : a % b = 0) : a / b * b = a :=
by rewrite [eq_div_mul_add_mod a b at {2}, H, add_zero]

theorem mul_div_cancel_of_mod_eq_zero {a b : ℤ} (H : a % b = 0) : b * (a / b) = a :=
!mul.comm ▸ div_mul_cancel_of_mod_eq_zero H

/- dvd -/

theorem dvd_of_of_nat_dvd_of_nat {m n : ℕ} : of_nat m ∣ of_nat n → (#nat m ∣ n) :=
nat.by_cases_zero_pos n
  (assume H, dvd_zero m)
  (take n' : ℕ,
    assume H1 : (#nat n' > 0),
    have H2 : of_nat n' > 0, from of_nat_pos H1,
    assume H3 : of_nat m ∣ of_nat n',
    dvd.elim H3
      (take c,
        assume H4 : of_nat n' = of_nat m * c,
        have H5 : c > 0, from pos_of_mul_pos_left (H4 ▸ H2) !of_nat_nonneg,
        obtain k (H6 : c = of_nat k), from exists_eq_of_nat (le_of_lt H5),
        have H7 : n' = (#nat m * k), from (of_nat.inj (H6 ▸ H4)),
        dvd.intro H7⁻¹))

theorem of_nat_dvd_of_nat_of_dvd {m n : ℕ} (H : #nat m ∣ n) : of_nat m ∣ of_nat n :=
dvd.elim H
  (take k, assume H1 : #nat n = m * k,
    dvd.intro (H1⁻¹ ▸ rfl))

theorem of_nat_dvd_of_nat_iff (m n : ℕ) : of_nat m ∣ of_nat n ↔ m ∣ n :=
iff.intro dvd_of_of_nat_dvd_of_nat of_nat_dvd_of_nat_of_dvd

theorem dvd.antisymm {a b : ℤ} (H1 : a ≥ 0) (H2 : b ≥ 0) : a ∣ b → b ∣ a → a = b :=
begin
  rewrite [-abs_of_nonneg H1, -abs_of_nonneg H2, -*of_nat_nat_abs],
  rewrite [*of_nat_dvd_of_nat_iff, *of_nat_eq_of_nat_iff],
  apply nat.dvd.antisymm
end

theorem dvd_of_mod_eq_zero {a b : ℤ} (H : b % a = 0) : a ∣ b :=
dvd.intro (!mul.comm ▸ div_mul_cancel_of_mod_eq_zero H)

theorem mod_eq_zero_of_dvd {a b : ℤ} (H : a ∣ b) : b % a = 0 :=
dvd.elim H (take z, assume H1 : b = a * z, H1⁻¹ ▸ !mul_mod_right)

theorem dvd_iff_mod_eq_zero (a b : ℤ) : a ∣ b ↔ b % a = 0 :=
iff.intro mod_eq_zero_of_dvd dvd_of_mod_eq_zero

definition dvd.decidable_rel [instance] : decidable_rel dvd :=
take a n, decidable_of_decidable_of_iff _ (iff.symm !dvd_iff_mod_eq_zero)

protected theorem div_mul_cancel {a b : ℤ} (H : b ∣ a) : a / b * b = a :=
div_mul_cancel_of_mod_eq_zero (mod_eq_zero_of_dvd H)

protected theorem mul_div_cancel' {a b : ℤ} (H : a ∣ b) : a * (b / a) = b :=
!mul.comm ▸ !int.div_mul_cancel H

protected theorem mul_div_assoc (a : ℤ) {b c : ℤ} (H : c ∣ b) : (a * b) / c = a * (b / c) :=
decidable.by_cases
  (assume cz : c = 0, by rewrite [cz, *int.div_zero, mul_zero])
  (assume cnz : c ≠ 0,
    obtain d (H' : b = d * c), from exists_eq_mul_left_of_dvd H,
    by rewrite [H', -mul.assoc, *(!int.mul_div_cancel cnz)])

theorem div_dvd_div {a b c : ℤ} (H1 : a ∣ b) (H2 : b ∣ c) : b / a ∣ c / a :=
have H3 : b = b / a * a, from (int.div_mul_cancel H1)⁻¹,
have H4 : c = c / a * a, from (int.div_mul_cancel (dvd.trans H1 H2))⁻¹,
decidable.by_cases
  (assume H5 : a = 0,
    have H6: c / a = 0, from (congr_arg _ H5 ⬝ !int.div_zero),
      H6⁻¹ ▸ !dvd_zero)
  (assume H5 : a ≠ 0,
    dvd_of_mul_dvd_mul_right H5 (H3 ▸ H4 ▸ H2))

protected theorem div_eq_iff_eq_mul_right {a b : ℤ} (c : ℤ) (H : b ≠ 0) (H' : b ∣ a) :
  a / b = c ↔ a = b * c :=
iff.intro
  (assume H1, by rewrite [-H1, int.mul_div_cancel' H'])
  (assume H1, by rewrite [H1, !int.mul_div_cancel_left H])

protected theorem div_eq_iff_eq_mul_left {a b : ℤ} (c : ℤ) (H : b ≠ 0) (H' : b ∣ a) :
  a / b = c ↔ a = c * b :=
!mul.comm ▸ !int.div_eq_iff_eq_mul_right H H'

protected theorem eq_mul_of_div_eq_right {a b c : ℤ} (H1 : b ∣ a) (H2 : a / b = c) :
  a = b * c :=
calc
  a     = b * (a / b) : int.mul_div_cancel' H1
    ... = b * c       : H2

protected theorem div_eq_of_eq_mul_right {a b c : ℤ} (H1 : b ≠ 0) (H2 : a = b * c) :
  a / b = c :=
calc
  a / b = b * c / b : H2
    ... = c         : !int.mul_div_cancel_left H1

protected theorem eq_mul_of_div_eq_left {a b c : ℤ} (H1 : b ∣ a) (H2 : a / b = c) :
  a = c * b :=
!mul.comm ▸ !int.eq_mul_of_div_eq_right H1 H2

protected theorem div_eq_of_eq_mul_left {a b c : ℤ} (H1 : b ≠ 0) (H2 : a = c * b) :
  a / b = c :=
int.div_eq_of_eq_mul_right H1 (!mul.comm ▸ H2)

theorem neg_div_of_dvd {a b : ℤ} (H : b ∣ a) : -a / b = -(a / b) :=
decidable.by_cases
  (assume H1 : b = 0, by rewrite [H1, *int.div_zero, neg_zero])
  (assume H1 : b ≠ 0,
    dvd.elim H
      (take c, assume H' : a = b * c,
        by rewrite [H', neg_mul_eq_mul_neg, *!int.mul_div_cancel_left H1]))

protected theorem sign_eq_div_abs (a : ℤ) : sign a = a / (abs a) :=
decidable.by_cases
  (suppose a = 0, by subst a)
  (suppose a ≠ 0,
    have abs a ≠ 0, from assume H, this (eq_zero_of_abs_eq_zero H),
    have abs a ∣ a, from abs_dvd_of_dvd !dvd.refl,
    eq.symm (iff.mpr (!int.div_eq_iff_eq_mul_left `abs a ≠ 0` this) !eq_sign_mul_abs))

theorem le_of_dvd {a b : ℤ} (bpos : b > 0) (H : a ∣ b) : a ≤ b :=
or.elim !le_or_gt
  (suppose a ≤ 0, le.trans this (le_of_lt bpos))
  (suppose a > 0,
    obtain c (Hc : b = a * c), from exists_eq_mul_right_of_dvd H,
    have a * c > 0, by rewrite -Hc; exact bpos,
    have c > 0, from pos_of_mul_pos_left this (le_of_lt `a > 0`),
    show a ≤ b, from calc
      a     = a * 1 : mul_one
        ... ≤ a * c : mul_le_mul_of_nonneg_left (add_one_le_of_lt `c > 0`) (le_of_lt `a > 0`)
        ... = b     : Hc)

/- / and ordering -/

protected theorem div_mul_le (a : ℤ) {b : ℤ} (H : b ≠ 0) : a / b * b ≤ a :=
calc
  a = a / b * b + a % b : eq_div_mul_add_mod
    ... ≥ a / b * b       : le_add_of_nonneg_right (!mod_nonneg H)

protected theorem div_le_of_le_mul {a b c : ℤ} (H : c > 0) (H' : a ≤ b * c) : a / c ≤ b :=
le_of_mul_le_mul_right (calc
  a / c * c = a / c * c + 0     : add_zero
        ... ≤ a / c * c + a % c : add_le_add_left (!mod_nonneg (ne_of_gt H))
        ... = a                 : eq_div_mul_add_mod
        ... ≤ b * c             : H') H

protected theorem div_le_self (a : ℤ) {b : ℤ} (H1 : a ≥ 0) (H2 : b ≥ 0) : a / b ≤ a :=
or.elim (lt_or_eq_of_le H2)
  (assume H3 : b > 0,
    have H4 : b ≥ 1, from add_one_le_of_lt H3,
    have H5 : a ≤ a * b, from calc
      a    = a * 1 : mul_one
       ... ≤ a * b : !mul_le_mul_of_nonneg_left H4 H1,
    int.div_le_of_le_mul H3 H5)
  (assume H3 : 0 = b,
    by rewrite [-H3, int.div_zero]; apply H1)

protected theorem mul_le_of_le_div {a b c : ℤ} (H1 : c > 0) (H2 : a ≤ b / c) : a * c ≤ b :=
calc
  a * c ≤ b / c * c : !mul_le_mul_of_nonneg_right H2 (le_of_lt H1)
    ... ≤ b           : !int.div_mul_le (ne_of_gt H1)

protected theorem le_div_of_mul_le {a b c : ℤ} (H1 : c > 0) (H2 : a * c ≤ b) : a ≤ b / c :=
have H3 : a * c < (b / c + 1) * c, from
  calc
    a * c ≤ b                 : H2
      ... = b / c * c + b % c : eq_div_mul_add_mod
      ... < b / c * c + c     : add_lt_add_left (!mod_lt_of_pos H1)
      ... = (b / c + 1) * c   : by rewrite [right_distrib, one_mul],
le_of_lt_add_one (lt_of_mul_lt_mul_right H3 (le_of_lt H1))

protected theorem le_div_iff_mul_le {a b c : ℤ} (H : c > 0) : a ≤ b / c ↔ a * c ≤ b :=
iff.intro (!int.mul_le_of_le_div H) (!int.le_div_of_mul_le H)

protected theorem div_le_div {a b c : ℤ} (H : c > 0) (H' : a ≤ b) : a / c ≤ b / c :=
int.le_div_of_mul_le H (le.trans (!int.div_mul_le (ne_of_gt H)) H')

protected theorem div_lt_of_lt_mul {a b c : ℤ} (H : c > 0) (H' : a < b * c) : a / c < b :=
lt_of_mul_lt_mul_right
  (calc
    a / c * c = a / c * c + 0       : add_zero
            ... ≤ a / c * c + a % c : add_le_add_left (!mod_nonneg (ne_of_gt H))
            ... = a                 : eq_div_mul_add_mod
            ... < b * c             : H')
 (le_of_lt H)

protected theorem lt_mul_of_div_lt {a b c : ℤ} (H1 : c > 0) (H2 : a / c < b) : a < b * c :=
assert H3 : (a / c + 1) * c ≤ b * c,
  from !mul_le_mul_of_nonneg_right (add_one_le_of_lt H2) (le_of_lt H1),
have H4 : a / c * c + c ≤ b * c, by rewrite [right_distrib at H3, one_mul at H3]; apply H3,
calc
  a     = a / c * c + a % c : eq_div_mul_add_mod
    ... < a / c * c + c     : add_lt_add_left (!mod_lt_of_pos H1)
    ... ≤ b * c             : H4

protected theorem div_lt_iff_lt_mul {a b c : ℤ} (H : c > 0) : a / c < b ↔ a < b * c :=
iff.intro (!int.lt_mul_of_div_lt H) (!int.div_lt_of_lt_mul H)

protected theorem div_le_iff_le_mul_of_div {a b : ℤ} (c : ℤ) (H : b > 0) (H' : b ∣ a) :
  a / b ≤ c ↔ a ≤ c * b :=
by rewrite [propext (!le_iff_mul_le_mul_right H), !int.div_mul_cancel H']

protected theorem le_mul_of_div_le_of_div {a b c : ℤ} (H1 : b > 0) (H2 : b ∣ a) (H3 : a / b ≤ c) :
  a ≤ c * b :=
iff.mp (!int.div_le_iff_le_mul_of_div H1 H2) H3

theorem div_pos_of_pos_of_dvd {a b : ℤ} (H1 : a > 0) (H2 : b ≥ 0) (H3 : b ∣ a) : a / b > 0 :=
have H4 : b ≠ 0, from
  (assume H5 : b = 0,
    have H6 : a = 0, from eq_zero_of_zero_dvd (H5 ▸ H3),
    ne_of_gt H1 H6),
have H6 : (a / b) * b > 0, by rewrite (int.div_mul_cancel H3); apply H1,
pos_of_mul_pos_right H6 H2

theorem div_eq_div_of_dvd_of_dvd {a b c d : ℤ} (H1 : b ∣ a) (H2 : d ∣ c) (H3 : b ≠ 0)
    (H4 : d ≠ 0) (H5 : a * d = b * c) :
  a / b = c / d :=
begin
  apply int.div_eq_of_eq_mul_right H3,
  rewrite [-!int.mul_div_assoc H2],
  apply eq.symm,
  apply int.div_eq_of_eq_mul_left H4,
  apply eq.symm H5
end

end int
