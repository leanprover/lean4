example : (fun x y => (0 + x) + (0 + y)) = Nat.add := by
  conv =>
    lhs
    intro x y
    repeat rw [Nat.zero_add]
