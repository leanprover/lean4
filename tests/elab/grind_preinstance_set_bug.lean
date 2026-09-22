module

/-!
Test that repeated E-matching makes no duplicate progress and that failed instantiation reports
the failure without suggesting a nonexistent tactic (#11996).
-/

opaque f : Nat → Nat
opaque g : Nat → Nat
theorem fax : f (x + 1) = g (f x) := sorry

/--
error: `instantiate` tactic failed to instantiate new facts
-/
#guard_msgs in
example : f (x + 5) = a := by
  grind =>
    use [fax]; use [fax]; use [fax]; use [fax]; use [fax];
    use [fax] -- Should fail - no new facts

/-- error: `instantiate` tactic failed to instantiate new facts -/
#guard_msgs in
example : False := by
  grind => instantiate only []
