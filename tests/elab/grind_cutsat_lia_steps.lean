module
set_option warn.sorry false

/-!
Tests the `liaSteps` threshold that interrupts the cutsat model search.

The "tight rhombus" example below requires enumerating thousands of cases during
Cooper conflict resolution. Without the threshold, `grind` used to spend a long time
searching and then produce a proof term so large that the kernel failed with a
deep-recursion error. With the default configuration, `grind` must fail quickly.
-/

example (x : Int) (y : Int)
    (h0 : ((0 <= ((27300 * x) - (24501 * y))) ∧ (((27300 * x) - (24501 * y)) <= 99) ∧
           (1 <= ((27301 * x) - (24500 * y))) ∧ (((27301 * x) - (24500 * y)) <= 100))) : False := by
  fail_if_success grind
  sorry

/-!
Checks that the `liaSteps` configuration option is wired: this example is solvable with
the default budget, but not with `liaSteps := 1`.
-/

example (x y : Int) :
    27 ≤ 11*x + 13*y →
    11*x + 13*y ≤ 45 →
    -10 ≤ 7*x - 9*y →
    7*x - 9*y ≤ 4 → False := by
  fail_if_success grind (liaSteps := 1)
  grind


/--
error: `grind` failed
case grind
x y : Int
h0 : 0 ≤ 27300 * x - 24501 * y ∧ 27300 * x - 24501 * y ≤ 99 ∧ 1 ≤ 27301 * x - 24500 * y ∧ 27301 * x - 24500 * y ≤ 100
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] -9100 * x + 8167 * y ≤ 0 ∧
          9100 * x + -8167 * y + -33 ≤ 0 ∧ -27301 * x + 24500 * y + 1 ≤ 0 ∧ 27301 * x + -24500 * y + -100 ≤ 0
  [eqc] True propositions
    [prop] -27301 * x + 24500 * y + 1 ≤ 0 ∧ 27301 * x + -24500 * y + -100 ≤ 0
    [prop] 9100 * x + -8167 * y + -33 ≤ 0 ∧ -27301 * x + 24500 * y + 1 ≤ 0 ∧ 27301 * x + -24500 * y + -100 ≤ 0
    [prop] -9100 * x + 8167 * y ≤ 0 ∧
          9100 * x + -8167 * y + -33 ≤ 0 ∧ -27301 * x + 24500 * y + 1 ≤ 0 ∧ 27301 * x + -24500 * y + -100 ≤ 0
    [prop] -27301 * x + 24500 * y + 1 ≤ 0
    [prop] 9100 * x + -8167 * y + -33 ≤ 0
    [prop] 27301 * x + -24500 * y + -100 ≤ 0
    [prop] -9100 * x + 8167 * y ≤ 0
  [limits] Thresholds reached
    [limit] maximum number of steps performed by the `lia` solver has been reached, threshold: `(liaSteps := 1)`
-/
#guard_msgs in
example (x : Int) (y : Int)
    (h0 : ((0 <= ((27300 * x) - (24501 * y))) ∧ (((27300 * x) - (24501 * y)) <= 99) ∧
           (1 <= ((27301 * x) - (24500 * y))) ∧ (((27301 * x) - (24500 * y)) <= 100))) : False := by
  grind (liaSteps := 1)
