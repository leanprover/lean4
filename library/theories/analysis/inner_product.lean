/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

Real inner product spaces.

Note: We can enter ⟨v, w⟩ as \<v, w\>.  This file overwrites the notation for dependent pairs.
-/
import theories.analysis.normed_space theories.analysis.sqrt
open nat real classical
noncomputable theory

structure inner_product_space [class] (V : Type) extends real_vector_space V :=
(inner : V → V → ℝ)
(inner_add_left : ∀ u v w, inner (add u v) w = inner u w + inner v w)
(inner_smul_left : ∀ r v w, inner (smul r v) w = r * inner v w)
(inner_comm : ∀ v w, inner v w = inner w v)
(inner_self_nonneg : ∀ v, inner v v ≥ 0)
(eq_zero_of_inner_self_eq_zero : ∀ {v}, inner v v = 0 → v = zero)

namespace analysis

variables {V : Type} [inner_product_space V]

definition inner (v w : V) : ℝ := inner_product_space.inner v w

notation `⟨` v `, ` w `⟩` := inner v w

proposition inner_comm (v w : V) : ⟨v, w⟩ = ⟨w, v⟩ := inner_product_space.inner_comm v w

proposition inner_add_left (u v w : V) : ⟨u + v, w⟩ = ⟨u, w⟩ + ⟨v, w⟩ :=
inner_product_space.inner_add_left u v w

proposition inner_add_right (u v w : V) : ⟨u, v + w⟩ = ⟨u, v⟩ + ⟨u, w⟩ :=
by rewrite [inner_comm, inner_add_left, inner_comm, inner_comm w]

proposition inner_smul_left (r : ℝ) (v w : V) : ⟨r • v, w⟩ = r * ⟨v, w⟩ :=
inner_product_space.inner_smul_left r v w

proposition inner_smul_right (r : ℝ) (v w : V) : ⟨v, r • w⟩ = r * ⟨v, w⟩ :=
by rewrite [inner_comm, inner_smul_left, inner_comm]

proposition inner_self_nonneg (v : V) : ⟨v, v⟩ ≥ 0 := inner_product_space.inner_self_nonneg v

proposition eq_zero_of_inner_self_eq_zero {v : V} (H : ⟨v, v⟩ = 0) : v = 0 :=
inner_product_space.eq_zero_of_inner_self_eq_zero H

proposition inner_neg_left (u v : V) : ⟨-u, v⟩ = -⟨u, v⟩ :=
by rewrite [-neg_one_smul_real, inner_smul_left, -neg_eq_neg_one_mul]

proposition inner_neg_right (u v : V) : ⟨u, -v⟩ = -⟨u, v⟩ :=
by rewrite [inner_comm, inner_neg_left, inner_comm]

proposition inner_sub_left (u v w : V) : ⟨u - v, w⟩ = ⟨u, w⟩ - ⟨v, w⟩ :=
by rewrite [*sub_eq_add_neg, inner_add_left, inner_neg_left]

proposition inner_sub_right (u v w : V) : ⟨u, v - w⟩ = ⟨u, v⟩ - ⟨u, w⟩ :=
by rewrite [*sub_eq_add_neg, inner_add_right, inner_neg_right]

proposition inner_zero_left (v : V) : ⟨0, v⟩ = 0 :=
have (0 : ℝ) • v = 0, from zero_smul v,
using this, by rewrite [-this, inner_smul_left, zero_mul]

proposition inner_zero_right (v : V) : ⟨v, 0⟩ = 0 :=
by rewrite [inner_comm, inner_zero_left]

definition orthogonal (u v : V) : Prop := ⟨u, v⟩ = 0

infix ` ⊥ `:50 := orthogonal

proposition orthogonal_comm {u v : V} (H : u ⊥ v) : v ⊥ u :=
by unfold orthogonal at *; rewrite [inner_comm, H]

/- first, we define norm internally, to show that an inner product space is a normed space -/

private definition ip_norm (v : V) : ℝ := sqrt ⟨v, v⟩

private proposition ip_norm_zero : ip_norm (0 : V) = 0 :=
by rewrite [↑ip_norm, inner_zero_left, sqrt_zero]

private proposition ip_norm_squared (v : V) : (ip_norm v)^2 = ⟨v, v⟩ :=
sqrt_squared (inner_self_nonneg v)

private proposition ip_norm_nonneg (v : V) : ip_norm v ≥ 0 := !sqrt_nonneg

private proposition eq_zero_of_ip_norm_eq_zero {v : V} (H : ip_norm v = 0) : v = 0 :=
have ⟨v, v⟩ = 0, by rewrite [-ip_norm_squared, H, pow_two, zero_mul],
eq_zero_of_inner_self_eq_zero this

private proposition ip_norm_smul (r : ℝ) (v : V) : ip_norm (r • v) = abs r * ip_norm v :=
begin
  rewrite [↑ip_norm, inner_smul_left, inner_smul_right, -mul.assoc],
  rewrite [sqrt_mul (mul_self_nonneg r) (inner_self_nonneg v), -pow_two, sqrt_squared']
end

private proposition ip_norm_pythagorean {u v : V} (ortho : u ⊥ v) :
    (ip_norm (u + v))^2 = (ip_norm u)^2 + (ip_norm v)^2 :=
by rewrite [↑orthogonal at ortho, *ip_norm_squared, inner_add_right, *inner_add_left,
            inner_comm v u, *ortho, zero_add, add_zero]

private definition ip_proj_on (u : V) {v : V} (H : v ≠ 0) : V :=
(⟨u, v⟩ / (ip_norm v)^2) • v

private proposition ip_proj_on_orthogonal (u : V) {v : V} (H : v ≠ 0) :
  ip_proj_on u H ⊥ (u - ip_proj_on u H) :=
begin
  rewrite [↑ip_proj_on, ↑orthogonal, inner_sub_right, +inner_smul_left, inner_smul_right],
  rewrite [ip_norm_squared at {3}],
  rewrite [div_mul_cancel _ (assume H', H (eq_zero_of_inner_self_eq_zero H'))],
  rewrite [inner_comm v u, sub_self]
end

private proposition ip_norm_proj_on_eq (u : V) {v : V} (H : v ≠ 0) :
  ip_norm (ip_proj_on u H) = abs ⟨u, v⟩ / ip_norm v :=
have H1 : ip_norm v ≠ 0, from assume H', H (eq_zero_of_ip_norm_eq_zero H'),
begin+
  rewrite [↑ip_proj_on, ip_norm_smul, abs_div, abs_of_nonneg (squared_nonneg (ip_norm v)), pow_two],
  rewrite [div_mul_eq_mul_div, -div_mul_div, div_self H1, mul_one]
end

private proposition ip_norm_squared_pythagorean (u : V) {v : V} (H : v ≠ 0) :
  (ip_norm u)^2 = (ip_norm (u - ip_proj_on u H))^2 + (ip_norm (ip_proj_on u H))^2 :=
calc
  (ip_norm u)^2 = (ip_norm (u - ip_proj_on u H + ip_proj_on u H))^2 :
                    sub_add_cancel
            ... = (ip_norm (u - ip_proj_on u H))^2 + (ip_norm (ip_proj_on u H))^2 :
                    ip_norm_pythagorean (orthogonal_comm (ip_proj_on_orthogonal u H))

private proposition ip_norm_proj_on_le (u : V) {v : V} (H : v ≠ 0) :
  ip_norm (ip_proj_on u H) ≤ ip_norm u :=
have (ip_norm u)^2 ≥ (ip_norm (ip_proj_on u H))^2,
  begin
    rewrite [ip_norm_squared_pythagorean u H],
    apply le_add_of_nonneg_left (squared_nonneg (ip_norm (u - ip_proj_on u H)))
  end,
le_of_squared_le_squared !ip_norm_nonneg this

private proposition ip_cauchy_schwartz (u v : V) : abs ⟨u, v⟩ ≤ ip_norm u * ip_norm v :=
by_cases
  (suppose v = (0 : V),
    begin
      rewrite [this, inner_zero_right, abs_zero, ip_norm_zero, mul_zero],
      exact le.refl (0 : ℝ)
    end)
  (assume vnz : v ≠ 0,
    have ip_norm v ≠ 0, from assume H, vnz (eq_zero_of_ip_norm_eq_zero H),
    have ip_norm v > 0, from lt_of_le_of_ne !sqrt_nonneg (ne.symm this),
    using this, begin
      note H := ip_norm_proj_on_le u vnz,
      rewrite [ip_norm_proj_on_eq u vnz at H],
      exact le_mul_of_div_le this H
    end)

private proposition ip_cauchy_schwartz' (u v : V) : ⟨u, v⟩ ≤ ip_norm u * ip_norm v :=
le.trans !le_abs_self !ip_cauchy_schwartz

private proposition ip_norm_triangle (u v : V) : ip_norm (u + v) ≤ ip_norm u + ip_norm v :=
have H : ⟨u, v⟩ ≤ ip_norm u * ip_norm v, from ip_cauchy_schwartz' u v,
have (ip_norm (u + v))^2 ≤ (ip_norm u + ip_norm v)^2, from
  calc
    (ip_norm (u + v))^2 = (ip_norm u)^2 + (ip_norm v)^2 + ⟨u, v⟩ + ⟨u, v⟩ :
            by rewrite [↑ip_norm, *sqrt_squared !inner_self_nonneg, inner_add_left,
                        *inner_add_right, *inner_comm v u, -add.assoc, -*add.right_comm _ _ ⟨v, v⟩]
    ... ≤ (ip_norm u)^2 + (ip_norm v)^2 + ip_norm u * ip_norm v + ⟨u, v⟩ :
            add_le_add_right (add_le_add_left H _) _
    ... ≤ (ip_norm u)^2 + (ip_norm v)^2 + ip_norm u * ip_norm v + ip_norm u * ip_norm v :
            add_le_add_left H _
    ... = (ip_norm u + ip_norm v)^2 :
            by rewrite [*pow_two, right_distrib, *left_distrib, -add.assoc,
                         *add.right_comm _ (ip_norm v * ip_norm v),
                         mul.comm (ip_norm v) (ip_norm u)],
le_of_squared_le_squared (add_nonneg !ip_norm_nonneg !ip_norm_nonneg) this

definition inner_product_space.to_normed_space [trans_instance] [reducible] :
  normed_vector_space V :=
⦃ normed_vector_space, _inst_1,
  norm                    := ip_norm,
  norm_zero               := ip_norm_zero,
  eq_zero_of_norm_eq_zero := @eq_zero_of_ip_norm_eq_zero V _,
  norm_triangle           := ip_norm_triangle,
  norm_smul               := ip_norm_smul
⦄

/- now we restate the new theorems using the norm notation -/

proposition norm_squared (v : V) : ∥ v ∥^2 = ⟨v, v⟩ := ip_norm_squared v

proposition norm_pythagorean {u v : V} (ortho : u ⊥ v) : ∥ u + v ∥^2 = ∥ u ∥^2 + ∥ v ∥^2 :=
ip_norm_pythagorean ortho

definition proj_on (u : V) {v : V} (H : v ≠ 0) : V := (⟨u, v⟩ / ∥ v ∥^2) • v

proposition proj_on_orthogonal (u : V) {v : V} (H : v ≠ 0) :
  proj_on u H ⊥ (u - proj_on u H) :=
ip_proj_on_orthogonal u H

proposition norm_proj_on_eq (u : V) {v : V} (H : v ≠ 0) :
  ∥ proj_on u H ∥ = abs ⟨u, v⟩ / ∥ v ∥ :=
ip_norm_proj_on_eq u H

proposition norm_squared_pythagorean (u : V) {v : V} (H : v ≠ 0) :
  ∥ u ∥^2 = ∥ u - proj_on u H ∥^2 + ∥ proj_on u H ∥^2 :=
ip_norm_squared_pythagorean u H

proposition norm_proj_on_le (u : V) {v : V} (H : v ≠ 0) :
  ∥ proj_on u H ∥ ≤ ∥ u ∥ := ip_norm_proj_on_le u H

theorem cauchy_schwartz (u v : V) : abs ⟨u, v⟩ ≤ ∥ u ∥ * ∥ v ∥ := ip_cauchy_schwartz u v

theorem cauchy_schwartz' (u v : V) : ⟨u, v⟩ ≤ ∥ u ∥ * ∥ v ∥ := ip_cauchy_schwartz' u v

theorem eq_proj_on_cauchy_schwartz {u v : V} (H : v ≠ 0) (H₁ : abs ⟨u, v⟩ = ∥ u ∥ * ∥ v ∥) :
  u = proj_on u H :=
assert ∥ v ∥ ≠ 0, from assume H', H (eq_zero_of_norm_eq_zero H'),
assert ∥ u ∥ = ∥ proj_on u H ∥, by rewrite [norm_proj_on_eq, H₁, mul_div_cancel _ this],
have ∥ u - proj_on u H ∥^2 + ∥ u ∥^2 = 0 + ∥ u ∥^2,
  by rewrite [zero_add, norm_squared_pythagorean u H at {2}, this],
have ∥ u - proj_on u H ∥^2 = 0, from eq_of_add_eq_add_right this,
show u = proj_on u H,
  from eq_of_sub_eq_zero (eq_zero_of_norm_eq_zero (eq_zero_of_squared_eq_zero this))

end analysis
