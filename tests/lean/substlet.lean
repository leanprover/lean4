theorem ex1 (n : Nat) : 0 + n = n := by
  let m := n
  have h : ∃ k, id k = m := ⟨m, rfl⟩
  cases h with
  | intro a e =>
    trace_state
    subst e
    trace_state
    apply Nat.zero_add

theorem ex2 (n : Nat) : 0 + n = n := by
  let m := n
  have h : ∃ k, m = id k := ⟨m, rfl⟩
  cases h with
  | intro a e =>
    trace_state
    subst e
    trace_state
    apply Nat.zero_add

theorem ex3 (n : Nat) (h : n = 0) : 0 + n = 0 := by
  let m := n + 1
  let v := m + 1
  have : v = n + 2 := rfl
  subst v -- error
  done
