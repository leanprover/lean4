import algebra.group

variable {A : Type}
variable [s : group A]
include s

set_option blast.cc.heq true

example (a : A) : a * 1⁻¹ = a :=
by inst_simp
