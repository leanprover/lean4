
/--
error: tactic 'decide' proved that the proposition
  False
is false
-/
#guard_msgs in
#eval show Nat from False.elim (by decide)

/--
error: aborting evaluation since the expression depends on the 'sorry' axiom, which can lead to runtime instability and crashes.

To attempt to evaluate anyway despite the risks, use the '#eval!' command.
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
#eval #[1,2,3][2]'sorry

/--
info: 3
---
warning: declaration uses 'sorry'
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
