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
  done
  fail_if_success done

/-!
Regression test: `all_goals` still respects recovery state.
-/
example (x y z : Option Int) : (x = y) ↔ (x = z) := by
  apply Iff.elim
  first | all_goals omega | all_goals sorry

/-!
Regression test: `all_goals` should not catch runtime exceptions.
-/
/--
error: maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
example : False := by
  all_goals repeat try trivial
  done
  fail_if_success done
