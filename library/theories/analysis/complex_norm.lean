/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

Instantiate the complex numbers as a normed space, by temporarily making it an inner product space
over the reals.
-/
import theories.analysis.inner_product data.complex
open nat real complex analysis classical
noncomputable theory

namespace complex
  namespace real_inner_product_space
    definition smul (a : ℝ) (z : ℂ) : ℂ := complex.mk (a * re z) (a * im z)

    definition ip (z w : ℂ) : ℝ := re z * re w + im z * im w

    proposition smul_left_distrib (a : ℝ) (z w : ℂ) : smul a (z + w) = smul a z + smul a w :=
    by rewrite [↑smul, *re_add, *im_add, *left_distrib]

    proposition smul_right_distrib (a b : ℝ) (z : ℂ) : smul (a + b) z = smul a z + smul b z :=
    by rewrite [↑smul, *right_distrib]

    proposition mul_smul (a b : ℝ) (z : ℂ) : smul (a * b) z = smul a (smul b z) :=
    by rewrite [↑smul, *mul.assoc]

    proposition one_smul (z : ℂ) : smul 1 z = z := by rewrite [↑smul, *one_mul, complex.eta]

    proposition inner_add_left (x y z : ℂ) : ip (x + y) z = ip x z + ip y z :=
    by rewrite [↑ip, re_add, im_add, *right_distrib, *add.assoc, add.left_comm (re y * re z)]

    proposition inner_smul_left (a : ℝ) (x y : ℂ) : ip (smul a x) y = a * ip x y :=
    by rewrite [↑ip, ↑smul, left_distrib, *mul.assoc]

    proposition inner_comm (x y : ℂ) : ip x y = ip y x :=
    by rewrite [↑ip, mul.comm, mul.comm (im x)]

    proposition inner_self_nonneg (x : ℂ) : ip x x ≥ 0 :=
    add_nonneg (mul_self_nonneg (re x)) (mul_self_nonneg (im x))

    proposition eq_zero_of_inner_self_eq_zero {x : ℂ} (H : ip x x = 0) : x = 0 :=
    have re x = 0, from eq_zero_of_mul_self_add_mul_self_eq_zero H,
    have im x = 0, from eq_zero_of_mul_self_add_mul_self_eq_zero
                         (by rewrite [↑ip at H, add.comm at H]; exact H),
    by+ rewrite [-complex.eta, `re x = 0`, `im x = 0`]
  end real_inner_product_space

  protected definition real_inner_product_space [reducible] : inner_product_space ℂ :=
  ⦃ inner_product_space, complex.discrete_field,
    smul               := real_inner_product_space.smul,
    inner              := real_inner_product_space.ip,
    smul_left_distrib  := real_inner_product_space.smul_left_distrib,
    smul_right_distrib := real_inner_product_space.smul_right_distrib,
    mul_smul           := real_inner_product_space.mul_smul,
    one_smul           := real_inner_product_space.one_smul,
    inner_add_left     := real_inner_product_space.inner_add_left,
    inner_smul_left    := real_inner_product_space.inner_smul_left,
    inner_comm         := real_inner_product_space.inner_comm,
    inner_self_nonneg  := real_inner_product_space.inner_self_nonneg,
    eq_zero_of_inner_self_eq_zero := @real_inner_product_space.eq_zero_of_inner_self_eq_zero
  ⦄

  local attribute complex.real_inner_product_space [trans_instance]

  protected definition normed_vector_space [trans_instance] [reducible] : normed_vector_space ℂ :=
  _

  theorem norm_squared_eq_cmod (z : ℂ) : ∥ z ∥^2 = cmod z := by rewrite norm_squared
end complex
