def f91 (n : Nat) : Option Nat :=
  if n > 100
    then pure (n - 10)
    else f91 (n + 11) >>= f91
partial_fixpoint

theorem f91_spec_high (n : Nat) (h : 100 < n) : f91 n =  some (n - 10) := by
  unfold f91; simp [*]

theorem f91_spec_low (n : Nat) (h₂ : n ≤ 100) : f91 n = some 91 := by
  unfold f91
  have : ¬ (100 < n) := by simp [*]
  simp [*]
  by_cases n < 90
  · rw [f91_spec_low (n + 11) (by omega)]
    simp only [Option.some_bind]
    rw [f91_spec_low 91 (by omega)]
  · rw [f91_spec_high (n + 11) (by omega)]
    simp only [Nat.reduceSubDiff, Option.some_bind]
    by_cases h : n = 100
    · simp [*, f91]
    · exact f91_spec_low (n + 1) (by omega)

theorem f91_spec (n : Nat) : f91 n =  some (if n ≤ 100 then 91 else n - 10) := by
  by_cases h100 : n ≤ 100
  · simp [f91_spec_low, *]
  · simp [f91_spec_high, Nat.lt_of_not_le ‹_›, *]
