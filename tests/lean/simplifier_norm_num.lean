import algebra.numeral algebra.field
open algebra
     
namespace norm_num
universe l
constants (A : Type.{l}) (A_comm_ring : comm_ring A)
attribute A_comm_ring [instance]

set_option simplify.max_steps 5000000
set_option simplify.top_down false

lemma bit0_add_bit0_helper [simp] (a b : A) : bit0 a + bit0 b = bit0 (a + b) := bit0_add_bit0_helper a b (a+b) rfl
lemma add1_bit1_helper [simp] (a : A) : (bit1 a) + 1 = bit0 (a + 1) := add1_bit1_helper a (add1 a) rfl
lemma bit1_add_one_helper [simp] (a : A) : bit1 a + 1 = (bit1 a) + 1 := bit1_add_one_helper a (add1 (bit1 a)) rfl

lemma bit1_add_bit0_helper [simp] (a b : A) : bit1 a + bit0 b = bit1 (a + b) := bit1_add_bit0_helper a b (a + b) rfl
lemma bit1_add_bit1_helper [simp] (a b : A) : bit1 a + bit1 b = bit0 (a + b + 1) := bit1_add_bit1_helper a b (a + b) (a + b + 1) rfl rfl
lemma bit0_add_bit1_helper [simp] (a b : A) : bit0 a + bit1 b = bit1 (a + b) := bit0_add_bit1_helper a b (a + b) rfl
lemma one_add_bit1_helper [simp] (a : A) : 1 + bit1 a = bit1 a + 1 := one_add_bit1_helper a (bit1 a + 1) rfl

lemma bin_zero_add [simp] (a : A) : 0 + a = a := bin_zero_add a
lemma bin_add_zero [simp] (a : A) : a + 0 = a := bin_add_zero a
lemma one_add_one [simp] : (1:A) + 1 = 2 := one_add_one
lemma one_add_bit0 [simp] (a : A) : 1 + bit0 a = bit1 a := one_add_bit0 a
lemma bit0_add_one [simp] (a : A) : bit0 a + 1 = bit1 a := bit0_add_one a

lemma mul_bit0_helper0 [simp] (a b : A) : bit0 a * bit0 b = bit0 (bit0 a * b) := mul_bit0_helper (bit0 a) b (bit0 a * b) rfl
lemma mul_bit0_helper1 [simp] (a b : A) : bit1 a * bit0 b = bit0 (bit1 a * b) := mul_bit0_helper (bit1 a) b (bit1 a * b) rfl

lemma mul_bit1_helper0 [simp] (a b : A) : bit0 a * bit1 b = bit0 (bit0 a * b) + bit0 a := mul_bit1_helper (bit0 a) b (bit0 a * b) (bit0 (bit0 a * b) + bit0 a) rfl rfl
lemma mul_bit1_helper1 [simp] (a b : A) : bit1 a * bit1 b = bit0 (bit1 a * b) + bit1 a := mul_bit1_helper (bit1 a) b (bit1 a * b) (bit0 (bit1 a * b) + bit1 a) rfl rfl

lemma mul_zero [simp] (a : A) : a * 0 = 0 := mul_zero a
lemma zero_mul [simp] (a : A) : 0 * a = 0 := zero_mul a
lemma mul_one [simp] (a : A) : a * 1 = a := mul_one a
lemma one_mul [simp] (a : A) : 1 * a = a := one_mul a

end norm_num

open norm_num

#simplify eq 0 (0:A) + 1 
#simplify eq 0 (1:A) + 0 
#simplify eq 0 (1:A) + 1 
#simplify eq 0 (0:A) + 2 
#simplify eq 0 (1:A) + 2 
#simplify eq 0 (2:A) + 1 
#simplify eq 0 (3:A) + 1 
#simplify eq 0 (2:A) + 2 
#simplify eq 0 (4:A) + 1 
#simplify eq 0 (3:A) + 2 
#simplify eq 0 (2:A) + 3 
#simplify eq 0 (0:A) + 6 
#simplify eq 0 (3:A) + 3 
#simplify eq 0 (4:A) + 2 
#simplify eq 0 (5:A) + 1 
#simplify eq 0 (4:A) + 3 
#simplify eq 0 (1:A) + 6 
#simplify eq 0 (6:A) + 1 
#simplify eq 0 (5:A) + 28
#simplify eq 0 (0 : A) + (2 + 3) + 7
#simplify eq 0 (70 : A) + (33 + 2)
#simplify eq 0 (23000000000 : A) + 22000000000

#simplify eq 0 (0 : A) * 0
#simplify eq 0 (0 : A) * 1
#simplify eq 0 (0 : A) * 2
#simplify eq 0 (2 : A) * 0
#simplify eq 0 (1 : A) * 0
#simplify eq 0 (1 : A) * 1
#simplify eq 0 (2 : A) * 1
#simplify eq 0 (1 : A) * 2
#simplify eq 0 (2 : A) * 2
#simplify eq 0 (3 : A) * 2
#simplify eq 0 (2 : A) * 3
#simplify eq 0 (4 : A) * 1
#simplify eq 0 (1 : A) * 4
#simplify eq 0 (3 : A) * 3
#simplify eq 0 (3 : A) * 4
#simplify eq 0 (4 : A) * 4
#simplify eq 0 (11 : A) * 2
#simplify eq 0 (15 : A) * 6
#simplify eq 0 (123456 : A) * 123456
