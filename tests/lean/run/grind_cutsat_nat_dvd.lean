set_option grind.warning false

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
