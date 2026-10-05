module
import Lean

/-! Regression tests for reentrant semiring internalization (#15479). -/

open Lean.Grind

/--
error: `grind` failed
case grind.1.1.1.1.1
R : Type
inst : CommSemiring R
x : R
m n : Nat
h : ¬(x ^ (m + 1)) ^ (n + 2) = x ^ (2 * m + n + m * n + 2)
h_1 : m * n = 2 * m
h_2 : 2 * m + n = 2 * m
h_3 : 2 * m + n + m * n = 2 * m
h_4 : m = 2 * m
h_5 : n = 2 * m
⊢ False
-/
#guard_msgs in
example {R : Type} [CommSemiring R] (x : R) (m n : Nat) :
    (x ^ (m + 1)) ^ (n + 2) = x ^ (m * n + 2 * m + n + 2) := by
  grind (splits := 1) -verbose

/--
error: `grind` failed
case grind.1.1.1.1.1
R : Type
inst : Semiring R
x : R
m n : Nat
h : ¬(x ^ (m + 1)) ^ (n + 2) = x ^ (2 * m + n + m * n + 2)
h_1 : m * n = 2 * m
h_2 : 2 * m + n = 2 * m
h_3 : 2 * m + n + m * n = 2 * m
h_4 : m = 2 * m
h_5 : n = 2 * m
⊢ False
-/
#guard_msgs in
example {R : Type} [Semiring R] (x : R) (m n : Nat) :
    (x ^ (m + 1)) ^ (n + 2) = x ^ (m * n + 2 * m + n + 2) := by
  grind (splits := 1) -verbose
