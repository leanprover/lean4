theorem ex1 (h₁ : a = 0) (h₂ : a + b = 0 + 0) : b + 0 = 0 := by
  simp [h₁, h₂] at h₁ h₂
  simp [h₂]

theorem ex2 (h₁ : a = 0) (h₂ : a + b = 0 + 0) : b + 0 = 0 := by
  simp [h₁] at *
  simp [h₂]
