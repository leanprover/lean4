import algebra.group

variable {A : Type}
variable [s : group A]
include s

theorem mul.right_inv₁ (a : A) : a * a⁻¹ = 1 :=
by rewrite [-{a}inv_inv at {1}, mul.left_inv]
