import algebra.ring data.nat
open algebra

variables {A : Type}

section
variables [s : add_comm_monoid A]
include s

attribute add.comm [forward]
attribute add.assoc [forward]

set_option blast.simp   false
set_option blast.subst  false
set_option blast.ematch true

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

set_option blast.simp   false
set_option blast.subst  false
set_option blast.ematch true

theorem inv_mul_cancel_left (a b : A) : a⁻¹ * (a * b) = b :=
by blast

attribute mul_one [forward]
attribute inv_mul_cancel_right [forward]

-- TODO(Leo): check if qfc can get this one
-- theorem inv_eq_of_mul_eq_one {a b : A} (H : a * b = 1) : a⁻¹ = b :=
-- by blast
end
