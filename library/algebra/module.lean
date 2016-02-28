/-
Copyright (c) 2015 Nathaniel Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad

Modules and vector spaces over a ring.

(We use "left_module," which is more precise, because "module" is a keyword.)
-/
import algebra.field

structure has_scalar [class] (F V : Type) :=
(smul : F → V → V)

infixl ` • `:73 := has_scalar.smul

/- modules over a ring -/

structure left_module [class] (R M : Type) [ringR : ring R]
  extends has_scalar R M, add_comm_group M :=
(smul_left_distrib : ∀ (r : R) (x y : M), smul r (add x y) = (add (smul r x) (smul r y)))
(smul_right_distrib : ∀ (r s : R) (x : M), smul (ring.add r s) x = (add (smul r x) (smul s x)))
(mul_smul : ∀ r s x, smul (mul r s) x = smul r (smul s x))
(one_smul : ∀ x, smul one x = x)

section left_module
  variables {R M : Type}
  variable  [ringR : ring R]
  variable  [moduleRM : left_module R M]
  include   ringR moduleRM

  -- Note: the anonymous include does not work in the propositions below.

  proposition smul_left_distrib (a : R) (u v : M) : a • (u + v) = a • u + a • v :=
  !left_module.smul_left_distrib

  proposition smul_right_distrib (a b : R) (u : M) : (a + b) • u = a • u + b • u :=
  !left_module.smul_right_distrib

  proposition mul_smul (a : R) (b : R) (u : M) : (a * b) • u = a • (b • u) :=
  !left_module.mul_smul

  proposition one_smul (u : M) : (1 : R) • u = u := !left_module.one_smul

  proposition zero_smul (u : M) : (0 : R) • u = 0 :=
  have (0 : R) • u + 0 • u = 0 • u + 0, by rewrite [-smul_right_distrib, *add_zero],
  !add.left_cancel this

  proposition smul_zero (a : R) : a • (0 : M) = 0 :=
  have a • (0:M) + a • 0 = a • 0 + 0, by rewrite [-smul_left_distrib, *add_zero],
  !add.left_cancel this

  proposition neg_smul (a : R) (u : M) : (-a) • u = - (a • u) :=
  eq_neg_of_add_eq_zero (by rewrite [-smul_right_distrib, add.left_inv, zero_smul])

  proposition neg_one_smul (u : M) : -(1 : R) • u = -u :=
  by rewrite [neg_smul, one_smul]

  proposition smul_neg (a : R) (u : M) : a • (-u) = -(a • u) :=
  by rewrite [-neg_one_smul, -mul_smul, mul_neg_one_eq_neg, neg_smul]

  proposition smul_sub_left_distrib (a : R) (u v : M) : a • (u - v) = a • u - a • v :=
  by rewrite [sub_eq_add_neg, smul_left_distrib, smul_neg]

  proposition sub_smul_right_distrib (a b : R) (v : M) : (a - b) • v = a • v - b • v :=
  by rewrite [sub_eq_add_neg, smul_right_distrib, neg_smul]
end left_module

/- vector spaces -/

structure vector_space [class] (F V : Type) [fieldF : field F]
  extends left_module F V
