def f' (n : Nat) : Option { r : Nat // r ≤ n } :=
  match n with
  | 0   => some ⟨0, Nat.le_refl _⟩
  | n+1 => match f' n with
    | some ⟨m, h₁⟩ =>
      have : m < n+1 := Nat.lt_of_le_of_lt h₁ (Nat.lt_succ_self _)
      match f' m with
      | some ⟨r, h₂⟩ => some ⟨r, Nat.le_trans h₂ (Nat.le_trans h₁ (Nat.le_succ _))⟩
      | none => none
    | none => none

theorem f'_ne_none (n : Nat) : f' n ≠ none := by
  match n with
  | 0   => simp (config := { decide := false }) [f']; done
  | n+1 =>
    simp [f']
    have ih₁ := f'_ne_none n
    split
    next m h₁ he =>
      have : m < n+1 := Nat.lt_of_le_of_lt h₁ (Nat.lt_succ_self _)
      have ih₂ := f'_ne_none m
      split
      next => simp
      next h => contradiction
    next => contradiction
