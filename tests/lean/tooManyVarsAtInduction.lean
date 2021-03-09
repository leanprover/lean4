theorem ex1 (n : Nat) : 0 + n = n := by
  induction n with
  | succ x ih₁ ih₂ ih₃ => admit
  | zero => rfl

theorem ex2 (n : Nat) : 0 + n = n := by
  cases n with
  | succ x ih => admit
  | zero => rfl
