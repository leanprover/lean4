/-!
# Mentioning `set_option diagnostics true` depends on it not already being set
-/

/--
error: failed to synthesize
  Coe Nat Int

Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth Coe Nat Int

set_option diagnostics true

/--
error: failed to synthesize
  Coe Nat Int
-/
#guard_msgs in
#synth Coe Nat Int
