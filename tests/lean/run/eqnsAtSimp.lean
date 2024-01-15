mutual
  def isEven : Nat → Bool
    | 0 => true
    | n+1 => isOdd n
  decreasing_by
    simp [measure, invImage, InvImage, Nat.lt_wfRel]
    apply Nat.lt_succ_self

  def isOdd : Nat → Bool
    | 0 => false
    | n+1 => isEven n
  decreasing_by
    simp [measure, invImage, InvImage, Nat.lt_wfRel]
    apply Nat.lt_succ_self
end

theorem isEven_double (x : Nat) : isEven (2 * x) = true := by
  induction x with
  | zero => simp [isEven]
  | succ x ih => simp [Nat.mul_succ, Nat.add_succ, isEven, isOdd, ih]
