/-!
Tests for the experimental `grind.lia.vm` option, which checks linear `lia` refutations with a
single run of `Int.Internal.Linear.linCheckProg` in the kernel VM.
-/

set_option grind.lia.vm true

theorem t1 (x y z : Int) (h1 : x + y ≤ 3) (h2 : 2*y - z ≥ 5) (h3 : z ≥ x) (h4 : x ≥ 1) : False := by
  lia

/-- info: 't1' depends on axioms: [propext, Classical.choice, Quot.sound, Int.Internal.Linear.unsat_of_linCheck] -/
#guard_msgs in #print axioms t1

theorem t2 (a b c d : Int) (h1 : a ≤ b) (h2 : b ≤ c) (h3 : c ≤ d) (h4 : d < a) : False := by lia

/-- info: 't2' depends on axioms: [propext, Classical.choice, Quot.sound, Int.Internal.Linear.unsat_of_linCheck] -/
#guard_msgs in #print axioms t2

-- Single-step refutations keep the existing certificates.
theorem t3 (x y : Int) (h1 : 2*x + 4*y = 7) : False := by lia

/-- info: 't3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms t3

-- Coefficients beyond 64 bits keep the existing certificates.
example (x y : Int) (h1 : x ≤ 2^70 * y) (h2 : 2^70 * y ≤ x - 1) : False := by lia
