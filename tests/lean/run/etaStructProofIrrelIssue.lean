example (h : m = n) : (Fin.mk m h₁ : Fin k) = Fin.mk n h₂ := by
  apply (Fin.ext_iff ..).2
  exact h

example (h : m = n) : (Fin.mk m h₁ : Fin k) = Fin.mk n h₂ := by
  simp
  exact h
