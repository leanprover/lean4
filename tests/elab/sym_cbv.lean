/-! Tests for the `cbv` tactic in `grind`'s `sym =>` interactive mode. -/

example : Nat.succ 7 = 8 := by
  sym =>
    cbv

example (h : a = 8) : Nat.succ 7 = a := by
  sym =>
    cbv
    exact h.symm

example (h : Nat.succ 7 = a) : 8 = a := by
  sym =>
    cbv at h
    exact h

example (h : Nat.succ 7 = a) : Nat.succ 7 = a := by
  sym =>
    cbv at h ⊢
    exact h

example (h : Nat.succ 7 = a) : Nat.succ 7 = a := by
  sym =>
    cbv at *
    exact h
