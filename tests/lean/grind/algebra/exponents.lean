open Lean.Grind

section CommSemiring

-- from Mathlib.RingTheory.Localization.Ideal
theorem IsLocalization.map_radical.extracted_1 {R : Type u_1} [inst : CommSemiring R] (x s : R) : (s * x) ^ (n + 1) = s ^ n * x * (s * x ^ n) := by
  grind

-- from Mathlib.Algebra.Polynomial.Expand
theorem Polynomial.expand_char.extracted_1 {R : Type u} [inst : CommSemiring R] (n p : Nat) (C X : R) : C * X ^ (n * p) = C * (X ^ n) ^ p := by grind

end CommSemiring

section CommRing

variable (R : Type) [CommRing R]

example (a : R) (n m : Nat) : a^((n+m)^2) = a^(n^2 + 2*n*m + m^2) := by grind
example (a : R) (n m : Nat) : a^((n+m)^2) = a^(n^2) * a^(2*n*m) * a^(m^2) := by grind

-- from Mathlib.NumberTheory.Multiplicity
theorem pow_two_pow_sub_pow_two_pow.extracted_1_1 {x y : R} (d : Nat) :
    x ^ 2 ^ (d + 1) - y ^ 2 ^ (d + 1) = (x ^ 2 ^ d + y ^ 2 ^ d) * (x ^ 2 ^ d - y ^ 2 ^ d) := by
  grind

end CommRing


section Field

variable (F : Type) [Field F]

example (a : F) (n m : Int) : a^(n - m) = a^n / a^m := by grind

example (a : F) (n m : Int) : a^((n - m) * (n + m)) = a^(n^2) / a^(m^2) := by grind

end Field
