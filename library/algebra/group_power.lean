/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

The power operation on monoids and groups. We separate this from group, because it depends on
nat, which in turn depends on other parts of algebra.

We have "pow a n" for natural number powers, and "gpow a i" for integer powers. The notation
a^n is used for the first, but users can locally redefine it to gpow when needed.

Note: power adopts the convention that 0^0=1.
-/
import data.nat.basic data.int.basic

variables {A : Type}

structure has_pow_nat [class] (A : Type) :=
(pow_nat : A → nat → A)

definition pow_nat {A : Type} [s : has_pow_nat A] : A → nat → A :=
has_pow_nat.pow_nat

infix ` ^ ` := pow_nat

structure has_pow_int [class] (A : Type) :=
(pow_int : A → int → A)

definition pow_int {A : Type} [s : has_pow_int A] : A → int → A :=
has_pow_int.pow_int

namespace algebra
 /- monoid -/
section monoid
open nat

variable [s : monoid A]
include s

definition monoid.pow (a : A) : ℕ → A
| 0     := 1
| (n+1) := a * monoid.pow n

definition monoid_has_pow_nat [reducible] [instance] : has_pow_nat A :=
has_pow_nat.mk monoid.pow

theorem pow_zero (a : A) : a^0 = 1 := rfl
theorem pow_succ (a : A) (n : ℕ) : a^(succ n) = a * a^n := rfl

theorem pow_one (a : A) : a^1 = a := !mul_one
theorem pow_two (a : A) : a^2 = a * a :=
calc
  a^2 = a * (a * 1) : rfl
  ... = a * a       : mul_one
theorem pow_three (a : A) : a^3 = a * (a * a) :=
calc
  a^3 = a * (a * (a * 1)) : rfl
  ... = a * (a * a)       : mul_one
theorem pow_four (a : A) : a^4 = a * (a * (a * a))  :=
calc
  a^4 = a * a^3           : rfl
  ... = a * (a * (a * a)) : pow_three

theorem pow_succ' (a : A) : ∀n, a^(succ n) = a^n * a
| 0        := by rewrite [pow_succ, *pow_zero, one_mul, mul_one]
| (succ n) := by rewrite [pow_succ, pow_succ' at {1}, pow_succ, mul.assoc]

theorem one_pow : ∀ n : ℕ, 1^n = (1:A)
| 0        := rfl
| (succ n) := by rewrite [pow_succ, one_mul, one_pow]

theorem pow_add (a : A) (m n : ℕ) : a^(m + n) = a^m * a^n :=
begin
  induction n with n ih,
    {rewrite [nat.add_zero, pow_zero, mul_one]},
  rewrite [add_succ, *pow_succ', ih, mul.assoc]
end

theorem pow_mul (a : A) (m : ℕ) : ∀ n, a^(m * n) = (a^m)^n
| 0        := by rewrite [nat.mul_zero, pow_zero]
| (succ n) := by rewrite [nat.mul_succ, pow_add, pow_succ', pow_mul]

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
| (succ n) := by rewrite [*pow_succ', mul_pow, *mul.assoc, mul.left_comm a]

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
| (succ m) (succ n) := by rewrite [pow_succ' at {1}, pow_succ at {1}, pow_succ', pow_succ,
                            *mul.assoc, inv_mul_cancel_left, mul_inv_cancel_left, pow_inv_comm]

end nat

open int

definition gpow (a : A) : ℤ → A
| (of_nat n) := a^n
| -[1+n]     := (a^(nat.succ n))⁻¹

open nat

private lemma gpow_add_aux (a : A) (m n : nat) :
  gpow a ((of_nat m) + -[1+n]) = gpow a (of_nat m) * gpow a (-[1+n]) :=
or.elim (nat.lt_or_ge m (nat.succ n))
  (assume H : (m < nat.succ n),
    assert H1 : (#nat nat.succ n - m > nat.zero), from nat.sub_pos_of_lt H,
    calc
      gpow a ((of_nat m) + -[1+n]) = gpow a (sub_nat_nat m (nat.succ n))  : rfl
        ... = gpow a (-[1+ nat.pred (nat.sub (nat.succ n) m)])            : {sub_nat_nat_of_lt H}
        ... = (a ^ (nat.succ (nat.pred (nat.sub (nat.succ n) m))))⁻¹    : rfl
        ... = (a ^ (nat.succ n) * (a ^ m)⁻¹)⁻¹                        :
                by krewrite [succ_pred_of_pos H1, pow_sub a (nat.le_of_lt H)]
        ... = a ^ m * (a ^ (nat.succ n))⁻¹                            :
                by rewrite [mul_inv, inv_inv]
        ... = gpow a (of_nat m) * gpow a (-[1+n])                         : rfl)
  (assume H : (m ≥ nat.succ n),
    calc
      gpow a ((of_nat m) + -[1+n]) = gpow a (sub_nat_nat m (nat.succ n))  : rfl
        ... = gpow a (#nat m - nat.succ n)                                : {sub_nat_nat_of_ge H}
        ... = a ^ m * (a ^ (nat.succ n))⁻¹                                : pow_sub a H
        ... = gpow a (of_nat m) * gpow a (-[1+n])                         : rfl)

theorem gpow_add (a : A) : ∀i j : int, gpow a (i + j) = gpow a i * gpow a j
| (of_nat m) (of_nat n) := !pow_add
| (of_nat m) -[1+n]     := !gpow_add_aux
| -[1+m]     (of_nat n) := by rewrite [int.add.comm, gpow_add_aux, ↑gpow, -*inv_pow, pow_inv_comm]
| -[1+m]     -[1+n]     :=
  calc
    gpow a (-[1+m] + -[1+n]) = (a^(#nat nat.succ m + nat.succ n))⁻¹ : rfl
      ... = (a^(nat.succ m))⁻¹ * (a^(nat.succ n))⁻¹ : by rewrite [pow_add, pow_comm, mul_inv]
      ... = gpow a (-[1+m]) * gpow a (-[1+n])       : rfl

theorem gpow_comm (a : A) (i j : ℤ) : gpow a i * gpow a j = gpow a j * gpow a i :=
by rewrite [-*gpow_add, int.add.comm]
end group

section ordered_ring
open nat
variable [s : linear_ordered_ring A]
include s

theorem pow_pos {a : A} (H : a > 0) (n : ℕ) : a ^ n > 0 :=
  begin
    induction n,
    rewrite pow_zero,
    apply zero_lt_one,
    rewrite pow_succ',
    apply mul_pos,
    apply v_0, apply H
  end

theorem pow_ge_one_of_ge_one {a : A} (H : a ≥ 1) (n : ℕ) : a ^ n ≥ 1 :=
  begin
    induction n,
    rewrite pow_zero,
    apply le.refl,
    rewrite [pow_succ', -mul_one 1],
    apply mul_le_mul v_0 H zero_le_one,
    apply le_of_lt,
    apply pow_pos,
    apply gt_of_ge_of_gt H zero_lt_one
  end

local notation 2 := (1 : A) + 1

theorem pow_two_add (n : ℕ) : 2^n + 2^n = 2^(succ n) :=
  by rewrite [pow_succ', left_distrib, *mul_one]

end ordered_ring

/- additive monoid -/

section add_monoid
variable [s : add_monoid A]
include s
local attribute add_monoid.to_monoid [trans-instance]
open nat

definition nmul : ℕ → A → A := λ n a, a^n

infix [priority algebra.prio] `⬝` := nmul

theorem zero_nmul (a : A) : (0:ℕ) ⬝ a = 0 := pow_zero a
theorem succ_nmul (n : ℕ) (a : A) : nmul (succ n) a = a + (nmul n a) := pow_succ a n

theorem succ_nmul' (n : ℕ) (a : A) : succ n ⬝ a = nmul n a + a := pow_succ' a n

theorem nmul_zero (n : ℕ) : n ⬝ 0 = (0:A) := one_pow n

theorem one_nmul (a : A) : 1 ⬝ a = a := pow_one a

theorem add_nmul (m n : ℕ) (a : A) : (m + n) ⬝ a = (m ⬝ a) + (n ⬝ a) := pow_add a m n

theorem mul_nmul (m n : ℕ) (a : A) : (m * n) ⬝ a = m ⬝ (n ⬝ a) := eq.subst (nat.mul.comm n m) (pow_mul a n m)

theorem nmul_comm (m n : ℕ) (a : A) : (m ⬝ a) + (n ⬝ a) = (n ⬝ a) + (m ⬝ a) := pow_comm a m n

end add_monoid

/- additive commutative monoid -/

section add_comm_monoid
open nat
variable [s : add_comm_monoid A]
include s
local attribute add_comm_monoid.to_comm_monoid [trans-instance]

theorem nmul_add (n : ℕ) (a b : A) : n ⬝ (a + b) = (n ⬝ a) + (n ⬝ b) := mul_pow a b n

end add_comm_monoid

section add_group
variable [s : add_group A]
include s
local attribute add_group.to_group [trans-instance]

section nat
open nat
theorem nmul_neg (n : ℕ) (a : A) : n ⬝ (-a) = -(n ⬝ a) := inv_pow a n

theorem sub_nmul {m n : ℕ} (a : A) (H : m ≥ n) : (m - n) ⬝ a = (m ⬝ a) + -(n ⬝ a) := pow_sub a H

theorem nmul_neg_comm (m n : ℕ) (a : A) : (m ⬝ (-a)) + (n ⬝ a) = (n ⬝ a) + (m ⬝ (-a)) := pow_inv_comm a m n

end nat

open int

definition imul : ℤ → A → A := λ i a, gpow a i

theorem add_imul (i j : ℤ) (a : A) : imul (i + j) a = imul i a + imul j a :=
  gpow_add a i j

theorem imul_comm (i j : ℤ) (a : A) : imul i a + imul j a = imul j a + imul i a := gpow_comm a i j

end add_group

end algebra
