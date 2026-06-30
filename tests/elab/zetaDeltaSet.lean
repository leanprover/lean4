opaque f : Nat → Nat

example (a : Nat) : True := by
  let x := a
  have h1 : f x = 2 := sorry
  suffices f a = 2 by sorry
  simp only [h1, x]

example : True := by
  let x := 37
  have : x = 2 := sorry
  suffices 37 = 2 by sorry
  simp only [this, x]
