example : (0 : Nat) + 0 = 0 :=
  show 0 + 0 = 0 from rfl

example : (0 : Int) + 0 = 0 :=
  show 0 + 0 = 0 from rfl

example : Int :=
  show Nat from 0

example (x : Nat) : (x + 0) + y = x + y := by
  rw [show x + 0 = x from rfl]
