/-
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
-/
import algebra.ring algebra.numeral

namespace simplifier

namespace sum_of_monomials

attribute algebra.add.assoc [simp]
attribute algebra.add.comm [simp]
attribute algebra.add.left_comm [simp]

attribute algebra.mul.left_comm [simp]
attribute algebra.mul.comm [simp]
attribute algebra.mul.assoc [simp]

attribute algebra.left_distrib [simp]
attribute algebra.right_distrib [simp]

end sum_of_monomials

namespace units

attribute algebra.zero_add [simp]
attribute algebra.add_zero [simp]

attribute algebra.zero_mul [simp]
attribute algebra.mul_zero [simp]

attribute algebra.one_mul [simp]
attribute algebra.mul_one [simp]

end units

-- TODO(dhs): remove `add1` from the original lemmas and delete this
namespace numeral_helper
open algebra

theorem bit1_add_bit1 {A : Type} [s : algebra.add_comm_semigroup A]
  [s' : has_one A] (a b : A) : bit1 a + bit1 b = bit0 ((a + b) + 1)
  := bit1_add_bit1 a b

theorem one_add_bit1 {A : Type} [s : add_comm_semigroup A] [s' : has_one A] (a : A)
  : one + bit1 a = (bit1 a) + 1 := !add.comm

theorem bit1_add_one {A : Type} [s : add_comm_semigroup A] [s' : has_one A] (a : A)
  : bit1 a + one = bit0 (a + 1) := add1_bit1 a

end numeral_helper

namespace numeral

attribute one_add_bit0 [simp]
attribute bit0_add_one [simp]
attribute numeral_helper.one_add_bit1 [simp]
attribute numeral_helper.bit1_add_one [simp]
attribute one_add_one [simp]

attribute bit0_add_bit0 [simp]
attribute bit0_add_bit1 [simp]
attribute bit1_add_bit0 [simp]

attribute numeral_helper.bit1_add_bit1 [simp]

attribute algebra.one_mul [simp]
attribute algebra.mul_one [simp]

attribute mul_bit0 [simp]
attribute mul_bit1 [simp]

attribute algebra.zero_add [simp]
attribute algebra.add_zero [simp]

attribute algebra.zero_mul [simp]
attribute algebra.mul_zero [simp]

end numeral

end simplifier
