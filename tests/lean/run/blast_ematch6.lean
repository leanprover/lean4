import algebra.ring data.nat
open algebra

variables {A : Type}

section
variable [s : group A]
include s

set_option blast.strategy "ematch"

attribute mul_one      [forward]
attribute mul.assoc    [forward]
attribute mul.left_inv [forward]
attribute one_mul      [forward]

theorem inv_eq_of_mul_eq_one₁ {a b : A} (H : a * b = 1) : a⁻¹ = b :=
-- This is the kind of theorem that can be easily proved using superposition,
-- but cannot to be proved using E-matching.
-- To prove it using E-matching, we must provide the following auxiliary assertion.
-- E-matching can prove it automatically, and then it is trivial to prove the conclusion
-- using it.
-- Remark: this theorem can also be proved using model-based quantifier instantiation (MBQI) available in Z3.
-- So, we may be able to prove it using qcf.
assert a⁻¹ * 1 = b, by blast,
by blast

end
