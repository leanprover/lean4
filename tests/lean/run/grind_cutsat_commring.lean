open Lean.Grind

variable [CommRing R] [LinearOrder R] [OrderedRing R]
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
