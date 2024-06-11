example : True := by
  have : ∃ k, 5 = 2 + k := by
    rcases Nat.exists_eq_add_of_le (?_ : 2 ≤ 5) with ⟨k, hk⟩
    exact ⟨k, hk⟩
    · decide
  exact trivial

example (f : (n : Nat) → n = 1 → ∃ m, n = m) : True := by
  let n : Nat := 1
  obtain ⟨_, _⟩ := f n ?g1
  · exact trivial
  · exact rfl
