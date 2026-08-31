def f : Bool → Bool
  | true => true
  | false => false

example : f true = true := by simp!

/--
info: Try this:
  [apply] simp! only [f]
-/
#guard_msgs in
example : f true = true := by simp?!

/--
info: Try this:
  [apply] simp_all! only [f]
-/
#guard_msgs in
example : f true = true := by simp_all?!

/--
info: Try this:
  [apply] dsimp! only [f]
-/
#guard_msgs in
example : f true = true := by dsimp?!
