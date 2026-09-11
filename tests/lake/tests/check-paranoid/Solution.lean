/-! A solution every checker `lake check --paranoid` and `lake challenge --paranoid` run accepts. -/

theorem comm (n m : Nat) : n + m = m + n := by
  grind
