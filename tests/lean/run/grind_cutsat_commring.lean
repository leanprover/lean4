module
open Std Lean.Grind

variable [CommRing R] [LE R] [LT R] [LawfulOrderLT R] [IsLinearOrder R] [OrderedRing R]
example (a b : R) (h : 0 ≤ a * b) : 0 ≤ b * a := by grind
example (a b : R) (h : 7 ≤ a * b) : 7 ≤ b * a := by grind

example (a b : Int) (h : 0 ≤ a * b) : 0 ≤ b * a := by grind
example (a b : Int) (h : 7 ≤ a * b) : 7 ≤ b * a := by grind

example (a b : Nat) (h : 0 ≤ a * b) : 0 ≤ b * a := by grind
example (a b : Nat) (h : 7 ≤ a * b) : 7 ≤ b * a := by grind
example (a b : Nat) (h : 7 ≤ a * b + b) : 7 ≤ b + b * a := by grind

example (a b : Int) (h₁ : 2 ∣ a*b) (h₂ : 2 ∣ 2*b*a + 1 - a*b) : False := by grind
example (a b : Int) (h₁ : 2 ∣ a*b) : 2 ∣ b*a := by grind
example (a b : Int) (h₁ : 3 ∣ a*b + b + c) (h₂ : 3 ∣ b*a + b + c + 1) : False := by grind

example (a b : Nat) (h₁ : 2 ∣ a*b) (h₂ : 2 ∣ b*a + 1) : False := by grind
example (a b : Nat) (h₁ : 2 ∣ 2*a*b + b) (h₂ : 2 ∣ b + 2*b*a + 1) : False := by grind

example (a b : Int) (h : a + 1 = a * b) : 2 * b * a - 2 * a ≤ 2 := by grind
example (a b : Int) (h : a + 1 = b * a) : 2 * a * b - 2 * a ≤ 2 := by grind
example (a b : Int) (h : a + 1 = 3 * b * a) : 6 * a * b - 2 * a ≤ 2 := by grind
example (a b c : Int) (h₁ : a + 1 + c = b * a) (h₂ : c + 2*b*a = 0) : 6 * a * b - 2 * a ≤ 2 := by grind

example (a b : Nat) (h : a + a * b = 1) : 2 * b * a + 2 * a ≤ 2 := by grind
example (a b : Nat) (h : a + b * a = 1) : 2 * a * b + 2 * a ≤ 2 := by grind
example (a b : Nat) (h : a + 2 * b * a = 10) : 2 * a * b + a ≤ 10 := by grind
example (a b : Nat) (h : a + 2 * b * a = a^2 + b) : 2 * a * b ≤ b + a*a:= by grind

example (a b : Int) (h : a + 1 = b * a) : 2 * a * b - 2 * a ≤ 2 := by grind

example (a b : Int) (h₁ : a + 1 ≠ a * b) (h₂ : a * b ≤ a + 1) : b * a < a + 1 := by grind
example (a b : Int) (h₁ : a + 1 ≠ b * a) (h₂ : a * b ≤ a + 1) : b * a < a + 1 := by grind
example (a b : Int) (h₁ : a + 1 ≠ a * b * a) (h₂ : a * a * b ≤ a + 1) : b * a^2 < a + 1 := by grind

example (a b : Nat) (h₁ : a + 1 ≠ a * b) (h₂ : a * b ≤ a + 1) : b * a < a + 1 := by grind
example (a b : Nat) (h₁ : a + 1 ≠ b * a) (h₂ : a * b ≤ a + 1) : b * a < a + 1 := by grind
example (a b : Nat) (h₁ : a + 1 ≠ a * b * a) (h₂ : a * a * b ≤ a + 1) : b * a^2 < a + 1 := by grind
