def f : Bool → Bool
  | true => true
  | false => false

example : f true = true := by simp!

/--
info: Try this:
  simp! only [f]
-/
#guard_msgs in
example : f true = true := by simp?!

/--
info: Try this:
  simp_all! only [f]
-/
#guard_msgs in
example : f true = true := by simp_all?!

/--
info: Try this:
  dsimp! only [f]
-/
#guard_msgs in
example : f true = true := by dsimp?!
