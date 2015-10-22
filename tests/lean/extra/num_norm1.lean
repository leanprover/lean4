import algebra.numeral algebra.field data.nat
open algebra

variable {A : Type}
variable [s : comm_ring A]
include s

example : (1 : A) = 0 + 1 := by norm_num
example : (1 : A) = 1 + 0 := by norm_num
example : (2 : A) = 1 + 1 := by norm_num
example : (2 : A) = 0 + 2 := by norm_num
example : (3 : A) = 1 + 2 := by norm_num
example : (3 : A) = 2 + 1 := by norm_num
example : (4 : A) = 3 + 1 := by norm_num
example : (4 : A) = 2 + 2 := by norm_num
example : (5 : A) = 4 + 1 := by norm_num
example : (5 : A) = 3 + 2 := by norm_num
example : (5 : A) = 2 + 3 := by norm_num
example : (6 : A) = 0 + 6 := by norm_num
example : (6 : A) = 3 + 3 := by norm_num
example : (6 : A) = 4 + 2 := by norm_num
example : (6 : A) = 5 + 1 := by norm_num
example : (7 : A) = 4 + 3 := by norm_num
example : (7 : A) = 1 + 6 := by norm_num
example : (7 : A) = 6 + 1 := by norm_num
example : 33 = 5 + (28 : A) := by norm_num

example : (12 : A) = 0 + (2 + 3) + 7 := by norm_num
example : (105 : A) = 70 + (33 + 2) := by norm_num
example : (45000000000 : A) = 23000000000 + 22000000000 := by norm_num

example : (12 : A) - 4 - (5 + -2) = 5 := by norm_num
example : (12 : A) - 4 - (5 + -2) - 20 = -15 := by norm_num
exit

example : (0 : A) * 0 = 0 := by norm_num
example : (0 : A) * 1 = 0 := by norm_num
example : (0 : A) * 2 = 0 := by norm_num
example : (2 : A) * 0 = 0 := by norm_num
example : (1 : A) * 0 = 0 := by norm_num
example : (1 : A) * 1 = 1 := by norm_num
example : (2 : A) * 1 = 2 := by norm_num
example : (1 : A) * 2 = 2 := by norm_num
example : (2 : A) * 2 = 4 := by norm_num
example : (3 : A) * 2 = 6 := by norm_num
example : (2 : A) * 3 = 6 := by norm_num
example : (4 : A) * 1 = 4 := by norm_num
example : (1 : A) * 4 = 4 := by norm_num
example : (3 : A) * 3 = 9 := by norm_num
example : (3 : A) * 4 = 12 := by norm_num
example : (4 : A) * 4 = 16 := by norm_num
example : (11 : A) * 2 = 22 := by norm_num
example : (15 : A) * 6 = 90 := by norm_num
example : (123456 : A) * 123456 = 15241383936 := by norm_num
