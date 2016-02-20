/-
Copyright (c) 2015 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Jeremy Avigad

The square root function.
-/
import .ivt
open analysis real classical
noncomputable theory

private definition sqr_lb (x : ℝ) : ℝ := 0

private theorem sqr_lb_is_lb (x : ℝ) (H : x ≥ 0) : (sqr_lb x) * (sqr_lb x) ≤ x :=
  by rewrite [↑sqr_lb, zero_mul]; assumption

private definition sqr_ub (x : ℝ) : ℝ := x + 1

private theorem sqr_ub_is_ub (x : ℝ) (H : x ≥ 0) : (sqr_ub x) * (sqr_ub x) ≥ x :=
  begin
    rewrite [↑sqr_ub, left_distrib, mul_one, right_distrib, one_mul, {x + 1}add.comm, -*add.assoc],
    apply le_add_of_nonneg_left,
    repeat apply add_nonneg,
    apply mul_nonneg,
    repeat assumption,
    apply zero_le_one
  end

private theorem lb_le_ub (x : ℝ) (H : x ≥ 0) : sqr_lb x ≤ sqr_ub x :=
  begin
    rewrite [↑sqr_lb, ↑sqr_ub],
    apply add_nonneg,
    assumption,
    apply zero_le_one
  end

private lemma sqr_cts : continuous (λ x : ℝ, x * x) := continuous_mul_of_continuous id_continuous id_continuous

definition sqrt (x : ℝ) : ℝ :=
  if H : x ≥ 0 then
    some (intermediate_value_incr_weak sqr_cts (lb_le_ub x H) (sqr_lb_is_lb x H) (sqr_ub_is_ub x H))
  else 0

private theorem sqrt_spec {x : ℝ} (H : x ≥ 0) : sqrt x * sqrt x = x ∧ sqrt x ≥ 0 :=
  begin
    rewrite [↑sqrt, dif_pos H],
    note Hs := some_spec (intermediate_value_incr_weak sqr_cts (lb_le_ub x H)
                           (sqr_lb_is_lb x H) (sqr_ub_is_ub x H)),
    cases Hs with Hs1 Hs2,
    cases Hs2 with Hs2a Hs2b,
    exact and.intro Hs2b Hs1
  end

theorem sqrt_mul_self {x : ℝ} (H : x ≥ 0) : sqrt x * sqrt x = x := and.left (sqrt_spec H)

theorem sqrt_nonneg (x : ℝ) : sqrt x ≥ 0 :=
if H : x ≥ 0 then and.right (sqrt_spec H) else by rewrite [↑sqrt, dif_neg H]; exact le.refl 0

theorem sqrt_squared {x : ℝ} (H : x ≥ 0) : (sqrt x)^2 = x :=
by krewrite [pow_two, sqrt_mul_self H]

theorem sqrt_zero : sqrt (0 : ℝ) = 0 :=
have sqrt 0 * sqrt 0 = 0, from sqrt_mul_self !le.refl,
or.elim (eq_zero_or_eq_zero_of_mul_eq_zero this) (λ H, H) (λ H, H)

theorem sqrt_squared_of_nonneg {x : ℝ} (H : x ≥ 0) : sqrt (x^2) = x :=
have sqrt (x^2)^2 = x^2, from sqrt_squared (squared_nonneg x),
eq_of_squared_eq_squared_of_nonneg (sqrt_nonneg (x^2)) H this

theorem sqrt_squared' (x : ℝ) : sqrt (x^2) = abs x :=
have x^2 = (abs x)^2, by krewrite [+pow_two, -abs_mul, abs_mul_self],
using this, by rewrite [this, sqrt_squared_of_nonneg (abs_nonneg x)]

theorem sqrt_mul {x y : ℝ} (Hx : x ≥ 0) (Hy : y ≥ 0) : sqrt (x * y) = sqrt x * sqrt y :=
have (sqrt (x * y))^2 = (sqrt x * sqrt y)^2, from calc
  (sqrt (x * y))^2 = x * y                   : by rewrite [sqrt_squared (mul_nonneg Hx Hy)]
               ... = (sqrt x)^2 * (sqrt y)^2 : by rewrite [sqrt_squared Hx, sqrt_squared Hy]
               ... = (sqrt x * sqrt y)^2     : by krewrite [*pow_two]; rewrite [*mul.assoc,
                                                           mul.left_comm (sqrt y)],
eq_of_squared_eq_squared_of_nonneg !sqrt_nonneg (mul_nonneg !sqrt_nonneg !sqrt_nonneg) this
