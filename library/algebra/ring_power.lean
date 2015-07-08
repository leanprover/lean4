/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

Properties of the power operation in an ordered ring.

(Right now, this file is just a stub. More soon.)
-/
import .group_power
open nat

namespace algebra

variable {A : Type}

section linear_ordered_semiring
variable [s : linear_ordered_semiring A]
include s

theorem pow_pos_of_pos {x : A} (i : ℕ) (H : x > 0) : x^i > 0 :=
begin
  induction i with [j, ih],
    {show (1 : A) > 0, from zero_lt_one},
    {show x^(succ j) > 0, from mul_pos ih H}
end

theorem pow_nonneg_of_nonneg {x : A} (i : ℕ) (H : x ≥ 0) : x^i ≥ 0 :=
begin
  induction i with [j, ih],
    {show (1 : A) ≥ 0, from le_of_lt zero_lt_one},
    {show x^(succ j) ≥ 0, from mul_nonneg ih H}
end

theorem pow_le_pow_of_le {x y : A} (i : ℕ) (H₁ : 0 ≤ x) (H₂ : x ≤ y) : x^i ≤ y^i :=
begin
  induction i with [i, ih],
    {rewrite *pow_zero, apply le.refl},
  rewrite *pow_succ,
  have H : 0 ≤ y^i, from pow_nonneg_of_nonneg i (le.trans H₁ H₂),
  apply mul_le_mul ih H₂ H₁ H
end

theorem pow_ge_one {x : A} (i : ℕ) (xge1 : x ≥ 1) : x^i ≥ 1 :=
assert H : x^i ≥ 1^i, from pow_le_pow_of_le i (le_of_lt zero_lt_one) xge1,
by rewrite one_pow at H; exact H

set_option formatter.hide_full_terms false

theorem pow_gt_one {x : A} {i : ℕ} (xgt1 : x > 1) (ipos : i > 0) : x^i > 1 :=
assert xpos : x > 0, from lt.trans zero_lt_one xgt1,
begin
  induction i with [i, ih],
    {exfalso, exact !nat.lt.irrefl ipos},
  have xige1 : x^i ≥ 1, from pow_ge_one _ (le_of_lt xgt1),
  rewrite [pow_succ', -mul_one 1, ↑has_lt.gt],
  apply mul_lt_mul xgt1 xige1 zero_lt_one,
  apply le_of_lt xpos
end

end linear_ordered_semiring

end algebra
