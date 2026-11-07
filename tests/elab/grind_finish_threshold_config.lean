/-! The failure message of `finish` names the thresholds of its own configuration items. -/

opaque f : Nat → Nat

/-- warning: declaration uses `sorry` -/
#guard_msgs in
@[grind =] theorem f_succ (n : Nat) : f (n + 1) = f n + 1 := sorry

/--
error: `finish` has failed after reaching the thresholds `(instances := 5)` and `(ematch := 5)`, use `+verbose` to obtain diagnostic information
-/
#guard_msgs in
example (h : f 0 = 0) : f 30 = 31 := by
  grind => finish (instances := 5)

/--
error: `grind` has failed after reaching the thresholds `(instances := 5)` and `(ematch := 5)`, use `+verbose` to obtain diagnostic information
-/
#guard_msgs in
example (h : f 0 = 0) : f 30 = 31 := by
  grind (instances := 5)

/--
error: `finish` has failed after reaching the thresholds `(instances := 5)` and `(ematch := 5)`, use `+verbose` to obtain diagnostic information
-/
#guard_msgs in
example (h : f 0 = 0) : f 30 = 31 := by
  grind => set_config (instances := 5) in finish
