/-!
# `all_goals` should not consume error messages

https://github.com/leanprover/lean4/issues/4888
-/

/--
error: application type mismatch
  Nat.succ True
argument
  True
has type
  Prop : Type
but is expected to have type
  Nat : Type
-/
#guard_msgs in
theorem bug: True := by
 all_goals exact Nat.succ True
 trace "Did not get here"

/-!
Regression test: `all_goals` should admit goals rather than leaving metavariables.
-/
/--
error: omega could not prove the goal:
No usable constraints found. You may need to unfold definitions so `omega` can see linear arithmetic facts about `Nat` and `Int`, which may also involve multiplication, division, and modular remainder by constants.
---
error: omega could not prove the goal:
No usable constraints found. You may need to unfold definitions so `omega` can see linear arithmetic facts about `Nat` and `Int`, which may also involve multiplication, division, and modular remainder by constants.
---
error: omega could not prove the goal:
No usable constraints found. You may need to unfold definitions so `omega` can see linear arithmetic facts about `Nat` and `Int`, which may also involve multiplication, division, and modular remainder by constants.
---
error: omega could not prove the goal:
No usable constraints found. You may need to unfold definitions so `omega` can see linear arithmetic facts about `Nat` and `Int`, which may also involve multiplication, division, and modular remainder by constants.
-/
#guard_msgs in
theorem kernel_declaration_meta_variables (x y z : Option Int) : (x = y) ↔ (x = z) := by
  apply Iff.elim
  all_goals omega
  trace "Did not get here"

/-!
Regression test: `all_goals` still respects recovery state.
-/
/-- warning: declaration uses 'sorry' -/
#guard_msgs in
example (x y z : Option Int) : (x = y) ↔ (x = z) := by
  apply Iff.elim
  first | all_goals omega | all_goals sorry
