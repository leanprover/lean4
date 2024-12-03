example {P} [Decidable P] {f g : Nat → Nat} {x : Nat} : (if P then f else g) x = 37 := by
  split
  · guard_target =ₛ  f x = 37
    sorry
  · guard_target =ₛ  g x = 37
    sorry

example {P} [Decidable P] {f g : Nat → Nat} {x : Nat} {b : Bool} : (match b with | true => f | false => g) x = 37 := by
  split
  · guard_target =ₛ  f x = 37
    sorry
  · guard_target =ₛ  g x = 37
    sorry
