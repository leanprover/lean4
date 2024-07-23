
/--
error: tactic 'decide' proved that the proposition
  False
is false
---
error: Cannot evaluate expression that depends on the `sorry` axiom.
Use `#eval!` to evaluate nevertheless (which may cause lean to crash).
-/
#guard_msgs in
#eval show Nat from False.rec (by decide)

/--
warning: declaration uses 'sorry'
---
error: Cannot evaluate expression that depends on the `sorry` axiom.
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

/--
warning: declaration uses 'sorry'
---
info: 3
-/
#guard_msgs in
#eval! (#[1,2,3].pop)[2]'sorry
