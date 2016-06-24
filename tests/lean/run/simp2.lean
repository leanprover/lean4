import algebra.group
constants (A : Type.{1}) (A_cg : comm_group A) (x y z w : A)
attribute A_cg [instance]

open tactic
open simplifier.ac

example : x * y = y * x := by simp >> triv
example : x * y * z * w = ((w * z) * y) * x := by simp >> triv
example : x * y * z * w = ((z * w) * x) * y := by simp >> triv

open simplifier.unit
example : x * y * z * 1 * w = ((z * w * 1) * x) * y := by simp >> triv
