
example (n : Fin 25) (P : Fin 25 → Prop) : P 26 := by
  simp only [Fin.isValue]
  guard_target = P 1
  sorry

example (n : Fin 25) (P : Fin 25 → Prop) : P 25 := by
  simp only [Fin.isValue]
  guard_target = P 0
  sorry

example (n : Fin 25) (P : Fin 25 → Prop) : P 24 := by
  fail_if_success simp only [Fin.isValue]
  guard_target = P 24
  sorry
