namespace Nat

def dist (n m : Nat) :=
  n - m + (m - n)

example (n m : Nat) : dist n m = dist m n := by
  simp [dist.eq_def, Nat.add_comm]

example (n m : Nat) : dist n m = dist m n := by
  simp [Nat.dist.eq_def, Nat.add_comm]

theorem dist_comm (n m : Nat) : dist n m = dist m n := by
  simp [dist.eq_def, Nat.add_comm]

theorem dist_self (n : Nat) : dist n n = 0 := by simp [dist.eq_def]
