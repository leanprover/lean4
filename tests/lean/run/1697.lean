
/--
error: tactic 'decide' proved that the proposition
  False
is false
---
error: cannot evaluate expression that depends on the `sorry` axiom.
Use `#eval!` to evaluate nevertheless (which may cause lean to crash).
-/
#guard_msgs in
#eval show Nat from False.elim (by decide)

/--
warning: declaration uses 'sorry'
---
error: cannot evaluate expression that depends on the `sorry` axiom.
Use `#eval!` to evaluate nevertheless (which may cause lean to crash).
-/
#guard_msgs in
#eval #[1,2,3][2]'sorry

/--
warning: declaration uses 'sorry'
---
info: 3
-/
#guard_msgs in
#eval! #[1,2,3][2]'sorry


/-

With this test I wanted to show that `#eval!` can be used to do unsafe operations. Under
normal circumstances this actually works with the output below, but the `Linux Debug` CI build
catches it and complains. Maybe too bold to have this in the test suite.

/--
warning: declaration uses 'sorry'
---
info: 3
-/
#guard_msgs in
#eval! (#[1,2,3].pop)[2]'sorry

-/
