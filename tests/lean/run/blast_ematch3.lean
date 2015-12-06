import algebra.ring data.nat

namespace foo
variables {A : Type}

section
variables [s : add_comm_monoid A]
include s

attribute add.comm [forward]
attribute add.assoc [forward]

set_option blast.strategy "ematch"

theorem add_comm_three  (a b c : A) : a + b + c = c + b + a :=
by blast

theorem add.comm4 : ∀ (n m k l : A), n + m + (k + l) = n + k + (m + l) :=
by blast
end

section
variable [s : group A]
include s

attribute mul.assoc [forward]
attribute mul.left_inv [forward]
attribute one_mul [forward]

set_option blast.strategy "ematch"

theorem inv_mul_cancel_left (a b : A) : a⁻¹ * (a * b) = b :=
by blast
end
end foo
