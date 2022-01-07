mutual
  def isEven : Nat → Bool
    | 0 => true
    | n+1 => isOdd n
  def isOdd : Nat → Bool
    | 0 => false
    | n+1 => isEven n
end
termination_by measure fun | Sum.inl n => n | Sum.inr n => n
decreasing_by apply Nat.lt_succ_self

theorem isEven_double (x : Nat) : isEven (2 * x) = true := by
  induction x with
  | zero => simp
  | succ x ih =>
    unfold isEven
    trace_state
    rw [Nat.mul_succ, Nat.add_succ]
    simp
    unfold isOdd
    trace_state
    rw [Nat.add_succ]
    simp
    exact ih
