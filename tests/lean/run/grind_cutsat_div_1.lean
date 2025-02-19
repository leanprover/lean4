set_option grind.warning false
set_option pp.structureInstances false
open Int.Linear

theorem ex₁ (a : Int) (h₁ : 2 ∣ a) (h₂ : 2 ∣ 2*a + 1 - a) : False := by
  grind

theorem ex₂ (a b : Int) (h₀ : 2 ∣ a + 1) (h₁ : 2 ∣ b + a) (h₂ : 2 ∣ b + 2*a) : False := by
  grind

theorem ex₃ (a b : Int) (_ : 2 ∣ a + 1) (h₁ : 3 ∣ a + 3*b + a) (h₂ : 2 ∣ 3*b + a + 3 - b) (h₃ : 3 ∣ 3 * b + 2 * a + 1) : False := by
  grind

theorem ex₄ (f : Int → Int) (a b : Int) (_ : 2 ∣ f (f a) + 1) (h₁ : 3 ∣ f (f a) + 3*b + f (f a)) (h₂ : 2 ∣ 3*b + f (f a) + 3 - b) (h₃ : 3 ∣ 3 * b + 2 * f (f a) + 1) : False := by
  grind

#print ex₁
#print ex₂
#print ex₃
#print ex₄
