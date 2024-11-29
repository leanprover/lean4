set_option trace.split.debug true

example {P} [Decidable P] {f g : Nat → Nat} {x : Nat} : (if P then f else g) x = 37 := by
  split <;> sorry
