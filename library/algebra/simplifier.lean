/-
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
-/
import algebra.ring algebra.numeral

namespace simplifier

namespace empty
end empty

namespace iff
attribute eq_self_iff_true [simp]
end iff

-- TODO(dhs): make these [simp] rules in the global namespace
namespace neg_helper
    open algebra
    variables {A : Type} [s : ring A] (a b : A)
    include s
    lemma neg_mul1 : (- a) * b = - (a * b) := eq.symm !algebra.neg_mul_eq_neg_mul
    lemma neg_mul2 : a * (- b) = - (a * b) := eq.symm !algebra.neg_mul_eq_mul_neg
    lemma sub_def : a - b = a + (- b) := rfl
end neg_helper

namespace neg
attribute neg_helper.neg_mul1 [simp]
attribute neg_helper.neg_mul2 [simp]
attribute neg_helper.sub_def [simp]
attribute algebra.neg_neg [simp]
end neg

namespace unit
attribute algebra.zero_add [simp]
attribute algebra.add_zero [simp]

attribute algebra.zero_mul [simp]
attribute algebra.mul_zero [simp]

attribute algebra.one_mul [simp]
attribute algebra.mul_one [simp]
end unit

namespace ac
export simplifier.iff simplifier.neg simplifier.unit

attribute algebra.add.assoc [simp]
attribute algebra.add.comm [simp]
attribute algebra.add.left_comm [simp]

attribute algebra.mul.left_comm [simp]
attribute algebra.mul.comm [simp]
attribute algebra.mul.assoc [simp]

end ac

namespace distrib
attribute algebra.left_distrib [simp]
attribute algebra.right_distrib [simp]
end distrib

namespace som
export simplifier.ac simplifier.distrib
end som

namespace numeral

-- TODO(dhs): remove `add1` from the original lemmas and delete this
namespace numeral_helper
open algebra

theorem bit1_add_bit1 {A : Type} [s : add_comm_semigroup A]
  [s' : has_one A] (a b : A) : bit1 a + bit1 b = bit0 ((a + b) + 1)
  := norm_num.bit1_add_bit1 a b

theorem bit1_add_one {A : Type} [s : add_comm_semigroup A] [s' : has_one A] (a : A)
  : bit1 a + one = bit0 (a + 1) := norm_num.add1_bit1 a

theorem one_add_bit1 {A : Type} [s : add_comm_semigroup A] [s' : has_one A] (a : A)
  : one + bit1 a = bit0 (a + 1) := by rewrite [!add.comm, bit1_add_one]

lemma one_add_bit0 [simp] {A : Type} [s : add_comm_semigroup A] [s' : has_one A] (a : A)
  : 1 + bit0 a = bit1 a := norm_num.one_add_bit0 a

lemma bit0_add_one [simp] {A : Type} [s : add_comm_semigroup A] [s' : has_one A] (a : A)
  : bit0 a + 1 = bit1 a := norm_num.bit0_add_one a

lemma mul_bit0_helper0 [simp] {A : Type} [s : comm_ring A] (a b : A)
  : bit0 a * bit0 b = bit0 (bit0 a * b) := norm_num.mul_bit0_helper (bit0 a) b (bit0 a * b) rfl

lemma mul_bit0_helper1 [simp] {A : Type} [s : comm_ring A] (a b : A)
  : bit1 a * bit0 b = bit0 (bit1 a * b) := norm_num.mul_bit0_helper (bit1 a) b (bit1 a * b) rfl

lemma mul_bit1_helper0 [simp] {A : Type} [s : comm_ring A] (a b : A)
  : bit0 a * bit1 b = bit0 (bit0 a * b) + bit0 a := norm_num.mul_bit1_helper (bit0 a) b (bit0 a * b) (bit0 (bit0 a * b) + bit0 a) rfl rfl

lemma mul_bit1_helper1 [simp] {A : Type} [s : comm_ring A] (a b : A)
  : bit1 a * bit1 b = bit0 (bit1 a * b) + bit1 a := norm_num.mul_bit1_helper (bit1 a) b (bit1 a * b) (bit0 (bit1 a * b) + bit1 a) rfl rfl

end numeral_helper

export simplifier.ac

attribute norm_num.bit0_add_bit0 [simp]
attribute numeral_helper.bit1_add_one [simp]
attribute norm_num.bit1_add_bit0 [simp]
attribute numeral_helper.bit1_add_bit1 [simp]
attribute norm_num.bit0_add_bit1 [simp]
attribute numeral_helper.one_add_bit1 [simp]

attribute norm_num.one_add_one [simp]
attribute numeral_helper.one_add_bit0 [simp]
attribute numeral_helper.bit0_add_one [simp]

attribute numeral_helper.mul_bit0_helper0 [simp]
attribute numeral_helper.mul_bit0_helper1 [simp]
attribute numeral_helper.mul_bit1_helper0 [simp]
attribute numeral_helper.mul_bit1_helper1 [simp]

end numeral

end simplifier
