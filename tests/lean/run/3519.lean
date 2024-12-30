/--
info: Try this: simp only [x]
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example {P : Nat → Prop} : let x := 0; P x := by
  intro x
  simp? [x]
  sorry

/--
info: Try this: simp_all only [x]
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example {P : Nat → Prop} : let x := 0; P x := by
  intro x
  simp_all? [x]
  sorry
