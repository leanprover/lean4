import algebra.group
open algebra

variables {A : Type}
variables [s : group A]
include s
namespace foo
set_option blast.strategy "ematch"
attribute inv_inv mul.left_inv mul.assoc one_mul mul_one [forward]

theorem mul.right_inv (a : A) : a * a⁻¹ = 1 :=
calc
    a * a⁻¹ = (a⁻¹)⁻¹ * a⁻¹ : by blast
        ... = 1             : by blast

theorem mul.right_inv₂ (a : A) : a * a⁻¹ = 1 :=
by blast

theorem mul_inv_cancel_left (a b : A) : a * (a⁻¹ * b) = b :=
calc
    a * (a⁻¹ * b) = a * a⁻¹ * b : by blast
      ... = 1 * b               : by blast
      ... = b                   : by blast

theorem mul_inv_cancel_left₂ (a b : A) : a * (a⁻¹ * b) = b :=
by blast

theorem mul_inv (a b : A) : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
inv_eq_of_mul_eq_one
  (calc
    a * b * (b⁻¹ * a⁻¹) = a * (b * (b⁻¹ * a⁻¹)) : by blast
      ... = 1                                   : by blast)

theorem eq_of_mul_inv_eq_one {a b : A} (H : a * b⁻¹ = 1) : a = b :=
calc
    a = a * b⁻¹ * b : by blast
      ... = 1 * b   : by blast
      ... = b       : by blast


-- This is another theorem that can be easily proved using superposition,
-- but cannot to be proved using E-matching.
-- To prove it using E-matching, we must provide the following auxiliary step using calc.
theorem eq_of_mul_inv_eq_one₂ {a b : A} (H : a * b⁻¹ = 1) : a = b :=
calc
  a = a * b⁻¹ * b : by blast
... = b           : by blast
end foo
