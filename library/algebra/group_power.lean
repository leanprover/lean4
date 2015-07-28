/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

The power operation on monoids and groups. We separate this from group, because it depends on
nat, which in turn depends on other parts of algebra.

We have "pow a n" for natural number powers, and "ipow a i" for integer powers. The notation
a^n is used for the first, but users can locally redefine it to ipow when needed.

Note: power adopts the convention that 0^0=1.
-/
import data.nat.basic data.int.basic

namespace algebra

variables {A : Type}

/- monoid -/

section monoid
open nat
variable [s : monoid A]
include s

definition pow (a : A) : ℕ → A
| 0     := 1
| (n+1) := pow n * a

infix [priority algebra.prio] `^` := pow

theorem pow_zero (a : A) : a^0 = 1 := rfl
theorem pow_succ (a : A) (n : ℕ) : a^(succ n) = a^n * a := rfl

theorem pow_succ' (a : A) : ∀n, a^(succ n) = a * a^n
| 0        := by rewrite [pow_succ, *pow_zero, one_mul, mul_one]
| (succ n) := by rewrite [pow_succ, pow_succ' at {1}, pow_succ, mul.assoc]

theorem one_pow : ∀ n : ℕ, 1^n = (1:A)
| 0        := rfl
| (succ n) := by rewrite [pow_succ, mul_one, one_pow]

theorem pow_one (a : A) : a^1 = a := !one_mul

theorem pow_add (a : A) (m : ℕ) : ∀ n, a^(m + n) = a^m * a^n
| 0        := by rewrite [nat.add_zero, pow_zero, mul_one]
| (succ n) := by rewrite [add_succ, *pow_succ, pow_add, mul.assoc]

theorem pow_mul (a : A) (m : ℕ) : ∀ n, a^(m * n) = (a^m)^n
| 0        := by rewrite [nat.mul_zero, pow_zero]
| (succ n) := by rewrite [nat.mul_succ, pow_add, pow_succ, pow_mul]

theorem pow_comm (a : A) (m n : ℕ)  : a^m * a^n = a^n * a^m :=
by rewrite [-*pow_add, nat.add.comm]

end monoid

/- commutative monoid -/

section comm_monoid
open nat
variable [s : comm_monoid A]
include s

theorem mul_pow (a b : A) : ∀ n, (a * b)^n = a^n * b^n
| 0        := by rewrite [*pow_zero, mul_one]
| (succ n) := by rewrite [*pow_succ, mul_pow, *mul.assoc, mul.left_comm a]

end comm_monoid

section group
variable [s : group A]
include s

section nat
open nat
theorem inv_pow (a : A) : ∀n, (a⁻¹)^n = (a^n)⁻¹
| 0        := by rewrite [*pow_zero, one_inv]
| (succ n) := by rewrite [pow_succ, pow_succ', inv_pow, mul_inv]

theorem pow_sub (a : A) {m n : ℕ} (H : m ≥ n) : a^(m - n) = a^m * (a^n)⁻¹ :=
assert H1 : m - n + n = m, from nat.sub_add_cancel H,
have H2 : a^(m - n) * a^n = a^m, by rewrite [-pow_add, H1],
eq_mul_inv_of_mul_eq H2

theorem pow_inv_comm (a : A) : ∀m n, (a⁻¹)^m * a^n = a^n * (a⁻¹)^m
| 0 n               := by rewrite [*pow_zero, one_mul, mul_one]
| m 0               := by rewrite [*pow_zero, one_mul, mul_one]
| (succ m) (succ n) := by rewrite [pow_succ at {1}, pow_succ' at {1}, pow_succ, pow_succ',
                            *mul.assoc, inv_mul_cancel_left, mul_inv_cancel_left, pow_inv_comm]

end nat

open int

definition ipow (a : A) : ℤ → A
| (of_nat n) := a^n
| -[1+n]     := (a^(nat.succ n))⁻¹

private lemma ipow_add_aux (a : A) (m n : nat) :
  ipow a ((of_nat m) + -[1+n]) = ipow a (of_nat m) * ipow a (-[1+n]) :=
or.elim (nat.lt_or_ge m (nat.succ n))
  (assume H : (#nat m < nat.succ n),
    assert H1 : (#nat nat.succ n - m > nat.zero), from nat.sub_pos_of_lt H,
    calc
      ipow a ((of_nat m) + -[1+n]) = ipow a (sub_nat_nat m (nat.succ n))  : rfl
        ... = ipow a (-[1+ nat.pred (nat.sub (nat.succ n) m)])            : {sub_nat_nat_of_lt H}
        ... = (pow a (nat.succ (nat.pred (nat.sub (nat.succ n) m))))⁻¹    : rfl
        ... = (pow a (nat.succ n) * (pow a m)⁻¹)⁻¹                        :
                by rewrite [nat.succ_pred_of_pos H1, pow_sub a (nat.le_of_lt H)]
        ... = pow a m * (pow a (nat.succ n))⁻¹                            :
                by rewrite [mul_inv, inv_inv]
        ... = ipow a (of_nat m) * ipow a (-[1+n])                         : rfl)
  (assume H : (#nat m ≥ nat.succ n),
    calc
      ipow a ((of_nat m) + -[1+n]) = ipow a (sub_nat_nat m (nat.succ n))  : rfl
        ... = ipow a (#nat m - nat.succ n)                                : {sub_nat_nat_of_ge H}
        ... = pow a m * (pow a (nat.succ n))⁻¹                            : pow_sub a H
        ... = ipow a (of_nat m) * ipow a (-[1+n])                         : rfl)

theorem ipow_add (a : A) : ∀i j : int, ipow a (i + j) = ipow a i * ipow a j
| (of_nat m) (of_nat n) := !pow_add
| (of_nat m) -[1+n]     := !ipow_add_aux
| -[1+m]     (of_nat n) := by rewrite [int.add.comm, ipow_add_aux, ↑ipow, -*inv_pow, pow_inv_comm]
| -[1+m]     -[1+n]     :=
  calc
    ipow a (-[1+m] + -[1+n]) = (a^(#nat nat.succ m + nat.succ n))⁻¹ : rfl
      ... = (a^(nat.succ m))⁻¹ * (a^(nat.succ n))⁻¹ : by rewrite [pow_add, pow_comm, mul_inv]
      ... = ipow a (-[1+m]) * ipow a (-[1+n])       : rfl

theorem ipow_comm (a : A) (i j : ℤ) : ipow a i * ipow a j = ipow a j * ipow a i :=
by rewrite [-*ipow_add, int.add.comm]
end group

section ordered_ring
open nat
variable [s : linear_ordered_ring A]
include s

theorem pow_pos {a : A} (H : a > 0) (n : ℕ) : pow a n > 0 :=
  begin
    induction n,
    rewrite pow_zero,
    apply zero_lt_one,
    rewrite pow_succ,
    apply mul_pos,
    apply v_0, apply H
  end

theorem pow_ge_one_of_ge_one {a : A} (H : a ≥ 1) (n : ℕ) : pow a n ≥ 1 :=
  begin
    induction n,
    rewrite pow_zero,
    apply le.refl,
    rewrite [pow_succ, -{1}mul_one],
    apply mul_le_mul v_0 H zero_le_one,
    apply le_of_lt,
    apply pow_pos,
    apply gt_of_ge_of_gt H zero_lt_one
  end

local notation 2 := (1 : A) + 1

theorem pow_two_add (n : ℕ) : pow 2 n + pow 2 n = pow 2 (succ n) :=
  by rewrite [pow_succ, left_distrib, *mul_one]

end ordered_ring

end algebra
