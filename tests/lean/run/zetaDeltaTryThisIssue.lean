opaque f : Nat → Nat

/--
info: Try this: simp only [h1, x]
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example (a : Nat) : True := by
  let x := a
  have h1 : f x = 2 := sorry
  suffices f a = 2 by sorry
  let w := a + a
  simp? only [h1, w, x]

/--
info: Try this: simp only [this, x]
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example : True := by
  let x := 37
  let y := 34
  have : x = 2 := sorry
  suffices 37 = 2 by sorry
  simp? only [this, x, y]
