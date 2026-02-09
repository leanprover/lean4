open Lean Grind
variable (R : Type) (a b : R)

section CommSemiring
variable [CommSemiring R]

example (m n : Nat) : (m + n) • a = m • a + n • a := by grind
example (m n : Nat) : (m * n) • a = m • (n • a) := by grind
example (m n : Nat) : (m * n) • (a * b) = (m • a) * (n • b) := by grind

end CommSemiring

section CommRing
variable (R : Type) (a b : R)
variable [CommRing R]

example (m n : Nat) (a : R) : (m + n) • a = m • a + n • a := by grind
example (m n : Nat) (a : R) : (m * n) • a = m • (n • a) := by grind
example (m n : Nat) : (m * n) • (a * b) = (m • a) * (n • b) := by grind

example (m n : Int) : (m + n) • a = m • a + n • a := by grind
example (m n : Int) : (m * n) • a = m • (n • a) := by grind
example (m n : Int) : (m * n) • (a * b) = (m • a) * (n • b) := by grind

end CommRing
