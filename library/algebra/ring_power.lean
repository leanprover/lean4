/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

Properties of the power operation in various structures, including ordered rings and fields.
-/
import .group_power .ordered_field
open nat

variable {A : Type}

section semiring
variable [s : semiring A]
include s

definition semiring_has_pow_nat [reducible] [instance] : has_pow_nat A :=
monoid_has_pow_nat

theorem zero_pow {m : ℕ} (mpos : m > 0) : 0^m = (0 : A) :=
have h₁ : ∀ m : nat, (0 : A)^(succ m) = (0 : A),
  begin
    intro m, induction m,
      krewrite pow_one,
      apply zero_mul
  end,
obtain m' (h₂ : m = succ m'), from exists_eq_succ_of_pos mpos,
show 0^m = 0, by rewrite h₂; apply h₁

end semiring

section integral_domain
variable [s : integral_domain A]
include s

definition integral_domain_has_pow_nat [reducible] [instance] : has_pow_nat A :=
monoid_has_pow_nat

theorem eq_zero_of_pow_eq_zero {a : A} {m : ℕ} (H : a^m = 0) : a = 0 :=
or.elim (eq_zero_or_pos m)
  (suppose m = 0,
    by rewrite [`m = 0` at H, pow_zero at H]; apply absurd H (ne.symm zero_ne_one))
  (suppose m > 0,
    have h₁ : ∀ m, a^succ m = 0 → a = 0,
      begin
        intro m,
        induction m with m ih,
          {krewrite pow_one; intros; assumption},
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
          { krewrite pow_one; assumption },
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
    {exfalso, exact !lt.irrefl ipos},
  have xige1 : x^i ≥ 1, from pow_ge_one _ (le_of_lt xgt1),
  rewrite [pow_succ, -mul_one 1],
  apply mul_lt_mul xgt1 xige1 zero_lt_one,
  apply le_of_lt xpos
end

theorem squared_lt_squared {x y : A} (H1 : 0 ≤ x) (H2 : x < y) : x^2 < y^2 :=
by rewrite [*pow_two]; apply mul_self_lt_mul_self H1 H2

theorem squared_le_squared {x y : A} (H1 : 0 ≤ x) (H2 : x ≤ y) : x^2 ≤ y^2 :=
or.elim (lt_or_eq_of_le H2)
  (assume xlty, le_of_lt (squared_lt_squared H1 xlty))
  (assume xeqy, by rewrite xeqy; apply le.refl)

theorem lt_of_squared_lt_squared {x y : A} (H1 : y ≥ 0) (H2 : x^2 < y^2) : x < y :=
lt_of_not_ge (assume H : x ≥ y, not_le_of_gt H2 (squared_le_squared H1 H))

theorem le_of_squared_le_squared {x y : A} (H1 : y ≥ 0) (H2 : x^2 ≤ y^2) : x ≤ y :=
le_of_not_gt (assume H : x > y, not_lt_of_ge H2 (squared_lt_squared H1 H))

theorem eq_of_squared_eq_squared_of_nonneg {x y : A} (H1 : x ≥ 0) (H2 : y ≥ 0) (H3 : x^2 = y^2) :
  x = y :=
lt.by_cases
  (suppose x < y, absurd (eq.subst H3 (squared_lt_squared H1 this)) !lt.irrefl)
  (suppose x = y, this)
  (suppose x > y, absurd (eq.subst H3 (squared_lt_squared H2 this)) !lt.irrefl)

end linear_ordered_semiring

section decidable_linear_ordered_comm_ring
variable [s : decidable_linear_ordered_comm_ring A]
include s

definition decidable_linear_ordered_comm_ring_has_pow_nat [reducible] [instance] : has_pow_nat A :=
monoid_has_pow_nat

theorem abs_pow (a : A) (n : ℕ) : abs (a^n) = abs a^n :=
begin
  induction n with n ih,
    krewrite [*pow_zero, (abs_of_nonneg zero_le_one : abs (1 : A) = 1)],
  rewrite [*pow_succ, abs_mul, ih]
end

theorem squared_nonneg (x : A) : x^2 ≥ 0 := by rewrite [pow_two]; apply mul_self_nonneg

theorem eq_zero_of_squared_eq_zero {x : A} (H : x^2 = 0) : x = 0 :=
by rewrite [pow_two at H]; exact eq_zero_of_mul_self_eq_zero H

theorem abs_eq_abs_of_squared_eq_squared {x y : A} (H : x^2 = y^2) : abs x = abs y :=
have (abs x)^2 = (abs y)^2, by rewrite [-+abs_pow, H],
eq_of_squared_eq_squared_of_nonneg (abs_nonneg x) (abs_nonneg y) this

end decidable_linear_ordered_comm_ring

section field
variable [s : field A]
include s

theorem field.div_pow (a : A) {b : A} {n : ℕ} (bnz : b ≠ 0) : (a / b)^n = a^n / b^n :=
begin
  induction n with n ih,
    krewrite [*pow_zero, div_one],
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
    krewrite [*pow_zero, div_one],
  rewrite [*pow_succ, ih, div_mul_div]
end

end discrete_field
