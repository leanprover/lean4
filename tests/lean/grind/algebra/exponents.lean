open Lean.Grind

section CommRing

variable (R : Type) [CommRing R]

example (a : R) (n : Nat) : a^(n + 1) = a^n * a := by grind
example (a : R) (n m : Nat) : a^(n + m) = a^n * a^m := by grind
example (a : R) (n m : Nat) : a^(n + m) = a^m * a^n := by grind
example (a : R) (n m : Nat) : a^(n + m + n) = a^m * a^(2*n) := by grind

example (n m : Nat) : (n+m)^2 = n^2 + 2*n*m + m^2 := by grind
example (a : R) (n m : Nat) : a^((n+m)^2) = a^(n^2 + 2*n*m + m^2) := by grind
example (a : R) (n m : Nat) : a^((n+m)^2) = a^(n^2) * a^(2*n*m) * a^(m^2) := by grind

end CommRing


section Field

variable (F : Type) [Field F]

example (a : F) (n m : Int) : a^(n + m - n) = a^m := by grind

example (a : F) (n m : Int) : a^(n - m) = a^n / a^m := by grind

example (a : F) (n m : Int) : a^((n - m) * (n + m)) = a^(n^2) / a^(m^2) := by grind

end Field
