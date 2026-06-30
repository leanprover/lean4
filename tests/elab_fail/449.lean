open Nat

theorem mul_comm (m n : Nat) : m * n = n * m := by
  induction n with
  | zero => simp
  | succ n ih =>
    have foo : m * n + m = m * n + (succ zero) * m := _
    rfl

theorem test (o : x ∨ y) : x := by
  cases o with
  | inl h => exact h
  | inr h => exact _
