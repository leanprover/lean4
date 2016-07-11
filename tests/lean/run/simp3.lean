import algebra.ring
constants (A : Type.{1}) (A_cr : comm_ring A) (x y z w : A)
attribute A_cr [instance]

open tactic

example : (x + y) * (z + w) = x * z + x * w + y * z + y * w * 1 + 0 :=
by simp

example : x + y = y + x := by simp
example : x + y + z = z + y + x := by simp
example : (x + y) * z = x * z + y * z := by simp
example : (x + y) * (z + w) = x * z + x * w + y * z + y * w := by simp
example : (x + y) * (z + w) = w * x + w * y + y * z + x * z := by simp
example : (x + y) * (z + w) = x * z + x * w + y * z + y * w * 1 + 0 := by simp
