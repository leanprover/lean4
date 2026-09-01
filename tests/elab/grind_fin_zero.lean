/-
Tests `grind` "knows" `toInt (0 : Fin n) = 0` even if `n` is not a numeral.
-/

example {n a : Nat} [NeZero n] {ha : a < n}  (h₁ : a ≠ 0) (h₂ : (⟨a, ha⟩ : Fin n) = 0) : False := by
  grind
