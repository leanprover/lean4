-- A function that reduced badly, as a canary for kernel reduction
def bad (n : Nat) : Nat :=
  if h : n = 0 then 0 else bad (n / 2)
termination_by n

theorem foo : 2 * bad 42000 = bad 42000 + bad 42000 := by simp_arith

theorem foo : Nat.mul 2 (bad 42000) = Nat.add (bad 42000) (bad 42000) := by simp_arith
