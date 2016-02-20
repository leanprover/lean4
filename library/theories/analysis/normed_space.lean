/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

Normed spaces.
-/
import algebra.module .metric_space
open real nat classical
noncomputable theory

structure has_norm [class] (M : Type) : Type :=
(norm : M → ℝ)

namespace analysis
  definition norm {M : Type} [has_normM : has_norm M] (v : M) : ℝ := has_norm.norm v

  notation `∥`v`∥` := norm v
end analysis

/- real vector spaces -/
-- where is the right place to put this?
structure real_vector_space [class] (V : Type) extends vector_space ℝ V

section
  variables {V : Type} [real_vector_space V]

  -- these specializations help the elaborator when it is hard to infer the ring, e.g. with numerals

  proposition smul_left_distrib_real (a : ℝ) (u v : V) : a • (u + v) = a • u + a • v :=
  smul_left_distrib a u v

  proposition smul_right_distrib_real (a b : ℝ) (u : V) : (a + b) • u = a • u + b • u :=
  smul_right_distrib a b u

  proposition mul_smul_real (a : ℝ) (b : ℝ) (u : V) : (a * b) • u = a • (b • u) :=
  mul_smul a b u

  proposition one_smul_real (u : V) : (1 : ℝ) • u = u := one_smul u

  proposition zero_smul_real (u : V) : (0 : ℝ) • u = 0 := zero_smul u

  proposition smul_zero_real (a : ℝ) : a • (0 : V) = 0 := smul_zero a

  proposition neg_smul_real (a : ℝ) (u : V) : (-a) • u = - (a • u) := neg_smul a u

  proposition neg_one_smul_real (u : V) : -(1 : ℝ) • u = -u := neg_one_smul u

  proposition smul_neg_real (a : ℝ) (u : V) : a • (-u) = -(a • u) := smul_neg a u
end

/- real normed vector spaces -/

structure normed_vector_space [class] (V : Type) extends real_vector_space V, has_norm V :=
(norm_zero : norm zero = 0)
(eq_zero_of_norm_eq_zero : ∀ u : V, norm u = 0 → u = zero)
(norm_triangle : ∀ u v, norm (add u v) ≤ norm u + norm v)
(norm_smul : ∀ (a : ℝ) (v : V), norm (smul a v) = abs a * norm v)

namespace analysis
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

  proposition norm_sub (u v : V) : ∥u - v∥ = ∥v - u∥ :=
    by rewrite [-norm_neg, neg_sub]

end analysis

section
  open analysis
  variable {V : Type}
  variable [normed_vector_space V]

  private definition nvs_dist [reducible] (u v : V) := ∥ u - v ∥

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

  definition normed_vector_space_to_metric_space [reducible] [trans_instance]
      (V : Type) [nvsV : normed_vector_space V] :
    metric_space V :=
  ⦃ metric_space,
    dist               := nvs_dist,
    dist_self          := nvs_dist_self,
    eq_of_dist_eq_zero := eq_of_nvs_dist_eq_zero,
    dist_comm          := nvs_dist_comm,
    dist_triangle      := nvs_dist_triangle
  ⦄

  open nat

  proposition converges_to_seq_norm_elim {X : ℕ → V} {x : V} (H : X ⟶ x in ℕ) :
    ∀ {ε : ℝ}, ε > 0 → ∃ N₁ : ℕ, ∀ {n : ℕ}, n ≥ N₁ → ∥ X n - x ∥ < ε := H

  proposition dist_eq_norm_sub (u v : V) : dist u v = ∥ u - v ∥ := rfl

  proposition norm_eq_dist_zero (u : V) : ∥ u ∥ = dist u 0 :=
  by rewrite [dist_eq_norm_sub, sub_zero]

  proposition norm_nonneg (u : V) : ∥ u ∥ ≥ 0 :=
  by rewrite norm_eq_dist_zero; apply !dist_nonneg
end

structure banach_space [class] (V : Type) extends nvsV : normed_vector_space V :=
(complete : ∀ X, @analysis.cauchy V (@normed_vector_space_to_metric_space V nvsV) X →
    @analysis.converges_seq V (@normed_vector_space_to_metric_space V nvsV) X)

definition banach_space_to_metric_space [reducible] [trans_instance]
    (V : Type) [bsV : banach_space V] :
  complete_metric_space V :=
⦃ complete_metric_space, normed_vector_space_to_metric_space V,
  complete := banach_space.complete
⦄

namespace analysis
variable {V : Type}
variable [normed_vector_space V]

variables {X Y : ℕ → V}
variables {x y : V}

proposition add_converges_to_seq (HX : X ⟶ x in ℕ) (HY : Y ⟶ y in ℕ) :
  (λ n, X n + Y n) ⟶ x + y in ℕ :=
take ε : ℝ, suppose ε > 0,
have e2pos : ε / 2 > 0, from  div_pos_of_pos_of_pos `ε > 0` two_pos,
obtain (N₁ : ℕ) (HN₁ : ∀ {n}, n ≥ N₁ → ∥ X n - x ∥ < ε / 2),
  from converges_to_seq_norm_elim HX e2pos,
obtain (N₂ : ℕ) (HN₂ : ∀ {n}, n ≥ N₂ → ∥ Y n - y ∥ < ε / 2),
  from converges_to_seq_norm_elim HY e2pos,
let N := max N₁ N₂ in
exists.intro N
  (take n,
    suppose n ≥ N,
    have ngtN₁ : n ≥ N₁, from nat.le_trans !le_max_left `n ≥ N`,
    have ngtN₂ : n ≥ N₂, from nat.le_trans !le_max_right `n ≥ N`,
    show ∥ (X n + Y n) - (x + y) ∥ < ε, from calc
      ∥ (X n + Y n) - (x + y) ∥
            = ∥ (X n - x) + (Y n - y) ∥   : by rewrite [sub_add_eq_sub_sub, *sub_eq_add_neg,
                                                         *add.assoc, add.left_comm (-x)]
        ... ≤ ∥ X n - x ∥ + ∥ Y n - y ∥   : norm_triangle
        ... < ε / 2 + ε / 2               : add_lt_add (HN₁ ngtN₁) (HN₂ ngtN₂)
        ... = ε                           : add_halves)

private lemma smul_converges_to_seq_aux {c : ℝ} (cnz : c ≠ 0) (HX : X ⟶ x in ℕ) :
  (λ n, c • X n) ⟶ c • x in ℕ :=
take ε : ℝ, suppose ε > 0,
have abscpos : abs c > 0, from abs_pos_of_ne_zero cnz,
have epos : ε / abs c > 0, from div_pos_of_pos_of_pos `ε > 0` abscpos,
obtain N (HN : ∀ {n}, n ≥ N → norm (X n - x) < ε / abs c), from converges_to_seq_norm_elim HX epos,
exists.intro N
  (take n,
    suppose n ≥ N,
    have H : norm (X n - x) < ε / abs c, from HN this,
    show norm (c • X n - c • x) < ε, from calc
      norm (c • X n - c • x)
            = abs c * norm (X n - x) : by rewrite [-smul_sub_left_distrib, norm_smul]
        ... < abs c * (ε / abs c)    : mul_lt_mul_of_pos_left H abscpos
        ... = ε                      : mul_div_cancel' (ne_of_gt abscpos))

proposition smul_converges_to_seq (c : ℝ) (HX : X ⟶ x in ℕ) :
  (λ n, c • X n) ⟶ c • x in ℕ :=
by_cases
  (assume cz : c = 0,
    have (λ n, c • X n) = (λ n, 0), from funext (take x, by rewrite [cz, zero_smul]),
    begin+ rewrite [this, cz, zero_smul], apply converges_to_seq_constant end)
  (suppose c ≠ 0, smul_converges_to_seq_aux this HX)

proposition neg_converges_to_seq (HX : X ⟶ x in ℕ) :
  (λ n, - X n) ⟶ - x in ℕ :=
take ε, suppose ε > 0,
obtain N (HN : ∀ {n}, n ≥ N → norm (X n - x) < ε), from converges_to_seq_norm_elim HX this,
exists.intro N
  (take n,
    suppose n ≥ N,
    show norm (- X n - (- x)) < ε,
      by rewrite [-neg_neg_sub_neg, *neg_neg, norm_neg]; exact HN `n ≥ N`)

proposition neg_converges_to_seq_iff : ((λ n, - X n) ⟶ - x in ℕ) ↔ (X ⟶ x in ℕ) :=
have aux : X = λ n, (- (- X n)), from funext (take n, by rewrite neg_neg),
iff.intro
  (assume H : (λ n, -X n)⟶ -x in ℕ,
    show X ⟶ x in ℕ, by+ rewrite [aux, -neg_neg x]; exact neg_converges_to_seq H)
  neg_converges_to_seq

proposition norm_converges_to_seq_zero (HX : X ⟶ 0 in ℕ) : (λ n, norm (X n)) ⟶ 0 in ℕ :=
take ε, suppose ε > 0,
obtain N (HN : ∀ n, n ≥ N → norm (X n - 0) < ε), from HX `ε > 0`,
exists.intro N
  (take n, assume Hn : n ≥ N,
    have norm (X n) < ε, begin rewrite -(sub_zero (X n)), apply HN n Hn end,
    show abs (norm (X n) - 0) < ε, using this,
      by rewrite [sub_zero, abs_of_nonneg !norm_nonneg]; apply this)

proposition converges_to_seq_zero_of_norm_converges_to_seq_zero
    (HX : (λ n, norm (X n)) ⟶ 0 in ℕ) :
  X ⟶ 0 in ℕ :=
take ε, suppose ε > 0,
obtain N (HN : ∀ n, n ≥ N → abs (norm (X n) - 0) < ε), from HX `ε > 0`,
exists.intro (N : ℕ)
  (take n : ℕ, assume Hn : n ≥ N,
    have HN' : abs (norm (X n) - 0) < ε, from HN n Hn,
    have norm (X n) < ε,
      by+ rewrite [sub_zero at HN', abs_of_nonneg !norm_nonneg at HN']; apply HN',
    show norm (X n - 0) < ε, using this,
      by rewrite sub_zero; apply this)

proposition norm_converges_to_seq_zero_iff (X : ℕ → V) :
  ((λ n, norm (X n)) ⟶ 0 in ℕ) ↔ (X ⟶ 0 in ℕ) :=
iff.intro converges_to_seq_zero_of_norm_converges_to_seq_zero norm_converges_to_seq_zero

end analysis
