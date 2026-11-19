module

import Init.Data.Nat.ExtendedGcd

/-!
Tests the extended Euclidean algorithm on natural numbers: zero conventions, signed Bézout
coefficients, arbitrary-precision inputs, long Euclidean chains, and the public correctness lemmas.
-/

#guard Nat.extendedGcd 0 0 = ⟨0, 0, 1⟩
#guard Nat.extendedGcd 0 19 = ⟨19, 0, 1⟩
#guard Nat.extendedGcd 19 0 = ⟨19, 1, 0⟩
#guard Nat.extendedGcd 19 19 = ⟨19, 1, 0⟩
#guard Nat.extendedGcd 240 46 = ⟨2, -9, 47⟩
#guard Nat.extendedGcd 46 240 = ⟨2, 47, -9⟩

-- These examples exercise kernel reduction rather than only compiled evaluation.
example : Nat.extendedGcd 240 46 = ⟨2, -9, 47⟩ := by decide +kernel
example : Nat.extendedGcd 46 240 = ⟨2, 47, -9⟩ := by decide +kernel
example : (Nat.extendedGcd (2 ^ 64) (2 ^ 64 + 1)).gcd = 1 := by decide +kernel

private def values : List Nat :=
  [0, 1, 2, 3, 6, 15, 46, 97, 240, 65536, 2 ^ 31 - 1, 2 ^ 32, 2 ^ 63 - 1, 2 ^ 63,
    2 ^ 64 - 1, 2 ^ 64, 2 ^ 64 + 1, 2 ^ 128 - 1, 2 ^ 128 + 1, 2 ^ 256 - 1]

private def correct (a b : Nat) : Bool :=
  let r := Nat.extendedGcd a b
  r.gcd == Nat.gcd a b && decide ((r.gcd : Int) = a * r.coeffA + b * r.coeffB) &&
    decide (r.gcd ∣ a ∧ r.gcd ∣ b)

#guard values.all fun a => values.all fun b => correct a b

private def fibPair (n : Nat) : Nat × Nat :=
  match n with
  | 0 => (0, 1)
  | n + 1 => let (a, b) := fibPair n; (b, a + b)

-- Consecutive Fibonacci numbers force many quotient-one Euclidean steps.
#guard [100, 256, 512].all fun n =>
  let (a, b) := fibPair n
  correct a b && (Nat.extendedGcd a b).gcd == 1

#guard (Nat.extendedGcd (240 * 2 ^ 128) (46 * 2 ^ 128)).gcd == 2 * 2 ^ 128

example (a b : Nat) : (Nat.extendedGcd a b).gcd = Nat.gcd a b := by simp

example (a b : Nat) :
    (Nat.gcd a b : Int) = a * (Nat.extendedGcd a b).coeffA + b * (Nat.extendedGcd a b).coeffB :=
  Nat.extendedGcd_bezout a b

example (b : Nat) : Nat.extendedGcd 0 b = ⟨b, 0, 1⟩ := by simp
example (a : Nat) (h : a ≠ 0) : Nat.extendedGcd a 0 = ⟨a, 1, 0⟩ := by simp [h]
example (a : Nat) (h : a ≠ 0) : Nat.extendedGcd a a = ⟨a, 1, 0⟩ := by simp [h]

example (a b : Nat) : (Nat.extendedGcd a b).gcd ∣ a := Nat.extendedGcd_dvd_left a b
example (a b : Nat) : (Nat.extendedGcd a b).gcd ∣ b := Nat.extendedGcd_dvd_right a b

-- A caller can retain one computed result and reason about it without exposing the algorithm.
example (a b : Nat) (r : Nat.ExtendedGcdResult) (h : r = Nat.extendedGcd a b)
    (hc : Nat.gcd a b = 1) : a * r.coeffA + b * r.coeffB = (1 : Int) := by
  subst r
  rw [← Nat.extendedGcd_bezout, hc, Int.natCast_one]
