module
example (x: Nat) : UInt32.size - x < UInt64.size := by
  grind only
