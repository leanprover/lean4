module

/-! Regression tests for reentrant semiring internalization (#15479). -/

open Lean.Grind

/--
error: `grind` has failed, use `+verbose` to obtain diagnostic information
-/
#guard_msgs in
example {R : Type} [CommSemiring R] (x : R) (m n : Nat) :
    (x ^ (m + 1)) ^ (n + 2) = x ^ (m * n + 2 * m + n + 2) := by
  grind (splits := 1) -verbose

/--
error: `grind` has failed, use `+verbose` to obtain diagnostic information
-/
#guard_msgs in
example {R : Type} [Semiring R] (x : R) (m n : Nat) :
    (x ^ (m + 1)) ^ (n + 2) = x ^ (m * n + 2 * m + n + 2) := by
  grind (splits := 1) -verbose
