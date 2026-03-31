def f91 (n : Nat) : Option Nat :=
  if n > 100
    then pure (n - 10)
    else f91 (n + 11) >>= f91
partial_fixpoint

section partial_correctness

-- #check f91.partial_correctness

theorem f91_partial_spec (n r : Nat) :
    f91 n = some r → r = if n > 100 then n - 10 else 91 := by
  apply f91.partial_correctness
  intro f91 ih n r h
  split at *
  · simp_all
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨r', hr1, hr2⟩ := h
    replace hr1 := ih _ _ hr1
    replace hr2 := ih _ _ hr2
    clear ih
    subst hr1
    subst hr2
    split
    · simp; omega
    · simp

end partial_correctness

section total_correctness

theorem f91_spec_high (n : Nat) (h : 100 < n) : f91 n =  some (n - 10) := by
  unfold f91; simp [*]

theorem f91_spec_low (n : Nat) (h₂ : n ≤ 100) : f91 n = some 91 := by
  unfold f91
  have : ¬ (100 < n) := by simp [*]
  simp [*]
  by_cases n < 90
  · rw [f91_spec_low (n + 11) (by omega)]
    simp only [Option.bind_some]
    rw [f91_spec_low 91 (by omega)]
  · rw [f91_spec_high (n + 11) (by omega)]
    simp only [Nat.reduceSubDiff, Option.bind_some]
    by_cases h : n = 100
    · set_option linter.loopingSimpArgs false in
      simp [*, f91]
    · exact f91_spec_low (n + 1) (by omega)

theorem f91_spec (n : Nat) :
    f91 n = some (if n ≤ 100 then 91 else n - 10) := by
  by_cases h100 : n ≤ 100
  · simp [f91_spec_low, *]
  · simp [f91_spec_high, Nat.lt_of_not_le ‹_›, *]

end total_correctness
