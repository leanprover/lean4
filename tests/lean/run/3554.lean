def foo : Nat → Nat
| 0 => 0
| n+1 => foo n + 1

set_option debug.moduleNameAtTimeout false
/--
error: (deterministic) timeout, maximum number of heartbeats (100) has been reached
Use `set_option maxHeartbeats <num>` to set the limit.

Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
set_option maxHeartbeats 100 in
theorem bar : True := by
  simp [show foo 1000 = 1000 from rfl]

/--
info: theorem bar : True :=
sorry
-/
#guard_msgs in
#print bar

/--
error: maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
theorem bar2 : True := by
  simp [show foo 1000 = 1000 from rfl]

/--
info: theorem bar2 : True :=
sorry
-/
#guard_msgs in
#print bar2
