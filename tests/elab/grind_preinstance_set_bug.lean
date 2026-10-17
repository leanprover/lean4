module

/-!
Test that repeated E-matching makes no duplicate progress and that failed instantiation reports
the failure with guidance for inspecting theorem patterns (#11996).
-/

opaque f : Nat → Nat
opaque g : Nat → Nat
theorem fax : f (x + 1) = g (f x) := sorry

/--
error: `instantiate` tactic failed to instantiate new facts
Use `show_patterns` to inspect active theorem patterns, or `show_patterns [thm₁, ...]` to inspect specific theorems.
-/
#guard_msgs in
example : f (x + 5) = a := by
  grind =>
    use [fax]; use [fax]; use [fax]; use [fax]; use [fax];
    use [fax] -- Should fail - no new facts

/--
error: `instantiate` tactic failed to instantiate new facts
Use `show_patterns` to inspect active theorem patterns, or `show_patterns [thm₁, ...]` to inspect specific theorems.
-/
#guard_msgs in
example : False := by
  grind => instantiate only []
