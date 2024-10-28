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
 trivial
