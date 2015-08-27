/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

Properties of the power operation in an ordered ring or field.

(Right now, this file is just a stub. More soon.)
-/
import .group_power .ordered_field
open nat

namespace algebra

variable {A : Type}

section semiring
variable [s : semiring A]
include s

theorem zero_pow {m : ℕ} (mpos : m > 0) : 0^m = (0 : A) :=
have h₁ : ∀ m, 0^succ m = (0 : A),
  from take m, nat.induction_on m
    (show 0^1 = 0, by rewrite pow_one)
    (take m, suppose 0^(succ m) = 0,
      show 0^(succ (succ m)) = 0, from !zero_mul),
obtain m' (h₂ : m = succ m'), from exists_eq_succ_of_pos mpos,
show 0^m = 0, by rewrite h₂; apply h₁

end semiring

section integral_domain
variable [s : integral_domain A]
include s

theorem eq_zero_of_pow_eq_zero {a : A} {m : ℕ} (H : a^m = 0) : a = 0 :=
or.elim (eq_zero_or_pos m)
  (suppose m = 0,
    by rewrite [`m = 0` at H, pow_zero at H]; apply absurd H (ne.symm zero_ne_one))
  (suppose m > 0,
    have h₁ : ∀ m, a^succ m = 0 → a = 0,
      begin
        intro m,
        induction m with m ih,
          {rewrite pow_one; intros; assumption},
        rewrite pow_succ,
        intro H,
        cases eq_zero_or_eq_zero_of_mul_eq_zero H with h₃ h₄,
          assumption,
        exact ih h₄
      end,
    obtain m' (h₂ : m = succ m'), from exists_eq_succ_of_pos `m > 0`,
    show a = 0, by rewrite h₂ at H; apply h₁ m' H)

theorem pow_ne_zero_of_ne_zero {a : A} {m : ℕ} (H : a ≠ 0) : a^m ≠ 0 :=
assume H', H (eq_zero_of_pow_eq_zero H')

end integral_domain

section division_ring
variable [s : division_ring A]
include s

theorem division_ring.pow_ne_zero_of_ne_zero {a : A} {m : ℕ} (H : a ≠ 0) : a^m ≠ 0 :=
or.elim (eq_zero_or_pos m)
  (suppose m = 0,
    by rewrite [`m = 0`, pow_zero]; exact (ne.symm zero_ne_one))
  (suppose m > 0,
    have h₁ : ∀ m, a^succ m ≠ 0,
      begin
        intro m,
        induction m with m ih,
          {rewrite pow_one; assumption},
        rewrite pow_succ,
        apply division_ring.mul_ne_zero H ih
      end,
    obtain m' (h₂ : m = succ m'), from exists_eq_succ_of_pos `m > 0`,
    show a^m ≠ 0, by rewrite h₂; apply h₁ m')

end division_ring

section linear_ordered_semiring
variable [s : linear_ordered_semiring A]
include s

theorem pow_pos_of_pos {x : A} (i : ℕ) (H : x > 0) : x^i > 0 :=
begin
  induction i with [j, ih],
    {show (1 : A) > 0, from zero_lt_one},
    {show x^(succ j) > 0, from mul_pos H ih}
end

theorem pow_nonneg_of_nonneg {x : A} (i : ℕ) (H : x ≥ 0) : x^i ≥ 0 :=
begin
  induction i with j ih,
    {show (1 : A) ≥ 0, from le_of_lt zero_lt_one},
    {show x^(succ j) ≥ 0, from mul_nonneg H ih}
end

theorem pow_le_pow_of_le {x y : A} (i : ℕ) (H₁ : 0 ≤ x) (H₂ : x ≤ y) : x^i ≤ y^i :=
begin
  induction i with i ih,
    {rewrite *pow_zero, apply le.refl},
  rewrite *pow_succ,
  have H : 0 ≤ x^i, from pow_nonneg_of_nonneg i H₁,
  apply mul_le_mul H₂ ih H (le.trans H₁ H₂)
end

theorem pow_ge_one {x : A} (i : ℕ) (xge1 : x ≥ 1) : x^i ≥ 1 :=
assert H : x^i ≥ 1^i, from pow_le_pow_of_le i (le_of_lt zero_lt_one) xge1,
by rewrite one_pow at H; exact H

theorem pow_gt_one {x : A} {i : ℕ} (xgt1 : x > 1) (ipos : i > 0) : x^i > 1 :=
assert xpos : x > 0, from lt.trans zero_lt_one xgt1,
begin
  induction i with [i, ih],
    {exfalso, exact !nat.lt.irrefl ipos},
  have xige1 : x^i ≥ 1, from pow_ge_one _ (le_of_lt xgt1),
  rewrite [pow_succ, -mul_one 1, ↑has_lt.gt],
  apply mul_lt_mul xgt1 xige1 zero_lt_one,
  apply le_of_lt xpos
end

end linear_ordered_semiring

section decidable_linear_ordered_comm_ring
variable [s : decidable_linear_ordered_comm_ring A]
include s

theorem abs_pow (a : A) (n : ℕ) : abs (a^n) = abs a^n :=
begin
  induction n with n ih,
    rewrite [*pow_zero, (abs_of_nonneg zero_le_one : abs (1 : A) = 1)],
  rewrite [*pow_succ, abs_mul, ih]
end

end decidable_linear_ordered_comm_ring

section field
variable [s : field A]
include s

theorem field.div_pow (a : A) {b : A} {n : ℕ} (bnz : b ≠ 0) : (a / b)^n = a^n / b^n :=
begin
  induction n with n ih,
    rewrite [*pow_zero, div_one],
  have bnnz : b^n ≠ 0, from division_ring.pow_ne_zero_of_ne_zero bnz,
  rewrite [*pow_succ, ih, !field.div_mul_div bnz bnnz]
end

end field

section discrete_field
variable [s : discrete_field A]
include s

theorem div_pow (a : A) {b : A} {n : ℕ} : (a / b)^n = a^n / b^n :=
begin
  induction n with n ih,
    rewrite [*pow_zero, div_one],
  rewrite [*pow_succ, ih, div_mul_div]
end

end discrete_field

end algebra
