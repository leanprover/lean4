/--
info: Try this: simp only [x]
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example {P : Nat → Prop} : let x := 0; P x := by
  intro x
  simp? [x] -- Try this: simp_all only
  sorry
