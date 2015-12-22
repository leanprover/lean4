/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

Normed spaces.
-/
import algebra.module .real_limit
open real

noncomputable theory

structure has_norm [class] (M : Type) : Type :=
(norm : M → ℝ)

definition norm {M : Type} [has_normM : has_norm M] (v : M) : ℝ := has_norm.norm v

notation `∥`v`∥` := norm v

-- where is the right place to put this?
structure real_vector_space [class] (V : Type) extends vector_space ℝ V

structure normed_vector_space [class] (V : Type) extends real_vector_space V, has_norm V :=
(norm_zero : norm zero = 0)
(eq_zero_of_norm_eq_zero : ∀ u : V, norm u = 0 → u = zero)
(norm_triangle : ∀ u v, norm (add u v) ≤ norm u + norm v)
(norm_smul : ∀ (a : ℝ) (v : V), norm (smul a v) = abs a * norm v)

-- what namespace should we put this in?

section normed_vector_space
  variable {V : Type}
  variable [normed_vector_space V]

  proposition norm_zero : ∥ (0 : V) ∥ = 0 := !normed_vector_space.norm_zero

  proposition eq_zero_of_norm_eq_zero {u : V} (H : ∥ u ∥ = 0) : u = 0 :=
  !normed_vector_space.eq_zero_of_norm_eq_zero H

  proposition norm_triangle (u v : V) : ∥ u + v ∥ ≤ ∥ u ∥ + ∥ v ∥ :=
  !normed_vector_space.norm_triangle

  proposition norm_smul (a : ℝ) (v : V) : ∥ a • v ∥ = abs a * ∥ v ∥ :=
  !normed_vector_space.norm_smul

  proposition norm_neg (v : V) : ∥ -v ∥ = ∥ v ∥ :=
  have abs (1 : ℝ) = 1, from abs_of_nonneg zero_le_one,
  by+ rewrite [-@neg_one_smul ℝ V, norm_smul, abs_neg, this, one_mul]

  section
    private definition nvs_dist (u v : V) := ∥ u - v ∥

    private lemma nvs_dist_self (u : V) : nvs_dist u u = 0 :=
    by rewrite [↑nvs_dist, sub_self, norm_zero]

    private lemma eq_of_nvs_dist_eq_zero (u v : V) (H : nvs_dist u v = 0) : u = v :=
    have u - v = 0, from eq_zero_of_norm_eq_zero H,
    eq_of_sub_eq_zero this

    private lemma nvs_dist_triangle (u v w : V) : nvs_dist u w ≤ nvs_dist u v + nvs_dist v w :=
    calc
      nvs_dist u w = ∥ (u - v) + (v - w) ∥       : by rewrite [↑nvs_dist, *sub_eq_add_neg, add.assoc,
                                                               neg_add_cancel_left]
               ... ≤ ∥ u - v ∥ + ∥ v - w ∥       : norm_triangle

    private lemma nvs_dist_comm  (u v : V) : nvs_dist u v = nvs_dist v u :=
    by rewrite [↑nvs_dist, -norm_neg, neg_sub]
  end

  definition normed_vector_space_to_metric_space [reducible] [trans_instance] : metric_space V :=
  ⦃ metric_space,
    dist               := nvs_dist,
    dist_self          := nvs_dist_self,
    eq_of_dist_eq_zero := eq_of_nvs_dist_eq_zero,
    dist_comm          := nvs_dist_comm,
    dist_triangle      := nvs_dist_triangle
  ⦄
end normed_vector_space

structure banach_space [class] (V : Type) extends nvsV : normed_vector_space V :=
(complete : ∀ X, @metric_space.cauchy V (@normed_vector_space_to_metric_space V nvsV) X →
    @metric_space.converges_seq V (@normed_vector_space_to_metric_space V nvsV) X)

definition banach_space_to_metric_space [reducible] [trans_instance] (V : Type) [bsV : banach_space V] :
  complete_metric_space V :=
⦃ complete_metric_space, normed_vector_space_to_metric_space,
  complete := banach_space.complete
⦄

section
  open metric_space

  example (V : Type) (vsV : banach_space V) (X : ℕ → V) (H : cauchy X) : converges_seq X :=
  complete V H
end

/- the real numbers themselves can be viewed as a banach space -/

definition real_is_real_vector_space [trans_instance] [reducible] : real_vector_space ℝ :=
⦃ real_vector_space, real.discrete_linear_ordered_field,
  smul               := mul,
  smul_left_distrib  := left_distrib,
  smul_right_distrib := right_distrib,
  smul_mul           := mul.assoc,
  one_smul           := one_mul
⦄

definition real_is_banach_space [trans_instance] [reducible] : banach_space ℝ :=
⦃ banach_space, real_is_real_vector_space,
  norm                    := abs,
  norm_zero               := abs_zero,
  eq_zero_of_norm_eq_zero := λ a H, eq_zero_of_abs_eq_zero H,
  norm_triangle           := abs_add_le_abs_add_abs,
  norm_smul               := abs_mul,
  complete                := λ X H, complete ℝ H
⦄
