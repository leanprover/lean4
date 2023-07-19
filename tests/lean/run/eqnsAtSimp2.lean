mutual
  @[simp] def isEven : Nat → Bool
    | 0 => true
    | n+1 => isOdd n
  @[simp] def isOdd : Nat → Bool
    | 0 => false
    | n+1 => isEven n
end
termination_by' measure fun
  | PSum.inl n => n
  | PSum.inr n => n
decreasing_by apply Nat.lt_succ_self

theorem isEven_double (x : Nat) : isEven (2 * x) = true := by
  induction x with
  | zero => simp
  | succ x ih => simp [Nat.mul_succ, Nat.add_succ, ih]

def f (x : Nat) : Nat :=
  match x with
  | 0 => 1
  | x + 1 => f x * 2
termination_by' measure id
decreasing_by apply Nat.lt_succ_self

attribute [simp] f

theorem f_succ (x : Nat) : f (x+1) = f x * 2 := by
  simp

theorem f_succ₂ (x : Nat) : f (x+1) = f x * 2 := by
  fail_if_success simp [-f]
  simp

attribute [-simp] f

theorem f_succ₃ (x : Nat) : f (x+1) = f x * 2 := by
  fail_if_success simp
  simp [f]
