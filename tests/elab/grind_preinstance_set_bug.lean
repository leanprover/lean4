opaque f : Nat → Nat
opaque g : Nat → Nat
theorem fax : f (x + 1) = g (f x) := sorry

/--
error: `instantiate` tactic failed to instantiate new facts, use `show_patterns` to see active theorems and their patterns.
-/
#guard_msgs in
example : f (x + 5) = a := by
  grind =>
    use [fax]; use [fax]; use [fax]; use [fax]; use [fax];
    use [fax] -- Should fail - no new facts
