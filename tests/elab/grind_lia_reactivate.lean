/-!
Variables created in a case of the `lia` model search survive backtracking as inactive variables:
the proofs of refuted cases may use them (#16228), but the constraints asserted when they were
created are rolled back. When such a variable is needed again, `mkVar` reactivates it and asserts
these constraints again.
-/

/-
`EqCnstr.elimNonUnit` creates the variable for `(1 * (3 * x / 6) + 0) / 3` in a Cooper case,
and creates it again in later cases.
-/
/--
trace: [grind.debug.lia.reactivate] 「(1 * (3 * x / 6) + 0) / 3」 ↦ #19
[grind.debug.lia.reactivate] 「(1 * (3 * x / 6) + 0) / 3」 ↦ #19
[grind.debug.lia.reactivate] 「(1 * (3 * x / 6) + 0) / 3」 ↦ #19
[grind.debug.lia.reactivate] 「(1 * (3 * x / 6) + 0) / 3」 ↦ #19
[grind.debug.lia.reactivate] 「(1 * (3 * x / 6) + 0) / 3」 ↦ #19
-/
#guard_msgs in
set_option trace.grind.debug.lia.reactivate true in
example (x : Int) : (-1 * x) % 6 ≠ (5 * x) % 6 → (3 * x) % 6 < (5 * x) / 6 → (3 * x) % 6 < (-2 * x) % 6 := by
  lia

/-
Nonlinear `%` propagation creates the variables for `↑y.toNat % 1` and `1` in a case (see #15622).
Reactivation asserts `0 ≤ ↑y.toNat % 1` and `1 = 1` again.
-/
/--
error: `grind` has failed, use `+verbose` to obtain diagnostic information
---
trace: [grind.debug.lia.reactivate] 「↑y.toNat % 1」 ↦ #36
[grind.debug.lia.reactivate] 「1」 ↦ #35
-/
#guard_msgs in
set_option trace.grind.debug.lia.reactivate true in
example (y : BitVec 1) (h : y % y < -(y * y)) : y + 1 = ~~~y + 1 := by
  grind
