def f (x : Nat) := x

theorem ex1 (h₁ : a = 0) (h₂ : a + b = 0) : f (b + c) = c := by
  simp_all
  simp [f]

theorem ex2 (h₁ : a = 0) (h₂ : a + b = 0) : f (b + c) = c := by
  simp_all [f]

theorem ex3 (h₁ : a = 0) (h₂ : a + b = 0) : f (b + c) = c := by
  simp_all only [f]
  rw [Nat.zero_add] at h₂
  simp [h₂]

theorem ex4 (h₁ : a = f a) (h₂ : b + 0 = 0) : f b = 0 := by
  simp_all [-h₁]

theorem ex5 (h₁ : a = f a) (h₂ : b + 0 = 0) : f (b + a) = a := by
  simp_all [-h₁, f]
