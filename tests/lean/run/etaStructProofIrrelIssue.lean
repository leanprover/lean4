theorem Fin.ext_iff : (Fin.mk m h₁ : Fin k) = Fin.mk n h₂ ↔ m = n :=
  Fin.mk.injEq _ _ _ _ ▸ Iff.rfl

example (h : m = n) : (Fin.mk m h₁ : Fin k) = Fin.mk n h₂ := by
  apply Fin.ext_iff.2
  exact h

example (h : m = n) : (Fin.mk m h₁ : Fin k) = Fin.mk n h₂ := by
  simp
  exact h
