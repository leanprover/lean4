module
theorem ex₁ (a : Nat) (h₁ : 2 ∣ a) (h₂ : 2 ∣ a + 1) : False := by
  grind

theorem ex₂ (a b : Nat) (h₀ : 2 ∣ a + 1) (h₁ : 2 ∣ b + a) (h₂ : 2 ∣ b + 2*a) : False := by
  grind

theorem ex₃ (a b : Nat) (_ : 2 ∣ a + 1) (h₁ : 3 ∣ a + 3*b + a) (h₂ : 2 ∣ 2*b + a + 3) (h₃ : 3 ∣ 3 * b + 2 * a + 1) : False := by
  grind

theorem ex₄ (a b : Nat) (h₀ : 1 - 1 + 1*2 ∣ a + 1) (h₁ : 2 ∣ b + a) (h₂ : 2 ∣ b + 2*a) : False := by
  grind

theorem ex₅ (x y : Nat) : 1 ≤ x + y → 100 ∣ x + y → 100 ≤ x + y := by
  grind

#print ex₁
#print ex₂
#print ex₃
#print ex₄
#print ex₅

example (x y : Nat) :
    5 ∣ x → ¬ 10 ∣ x
    → y = 7
    → x - y ≤ 2 → x ≥ 6
    → False := by
  grind

example (i : Nat) : i < 330 → 7 ∣ (660 + i) * (1319 - i) → 1319 - i < 1979 := by
  grind

example (x y : Nat) (_ : 2 ≤ x) (_ : x ≤ 3) (_ : 2 ≤ y) (_ : y ≤ 3) :
    4 ≤ (x + y) % 8 ∧ (x + y) % 8 ≤ 6 := by
  grind

example (x y : Nat) (_ : 2 ≤ x) (_ : x ≤ 3) (_ : 2 ≤ y) (_ : y ≤ 3) :
    4 ≤ (y + x) % 8 ∧ (x + y) % 8 ≤ 6 := by
  grind

example (x y : Nat) (_ : 2 ≤ x) (_ : x ≤ 3) (_ : 2 ≤ y) (_ : y ≤ 3) :
    4 ≤ (y + x) % 8 ∧ (y + x) % 8 ≤ 6 := by
  grind

example (i j k l : Nat) : i / j + k + l - k = i / j + l := by
  grind

example (i j k l : Nat) : i % j + k + l - k = i % j + l := by
  grind

example (i j k l : Nat) : i * j + k + l - k = i * j + l := by
  grind
