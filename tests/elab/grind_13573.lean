
/-!
The following nonlinear example should fail quickly without
a deterministic timeout.
-/

/--
error: `lia` has failed, use `+verbose` to obtain diagnostic information
-/
#guard_msgs in
example (x1 x2 x3 x4 x5 x6 x7 x8 : Int) :
    ¬x8 = x2 →
    x8 = x2 + ((x3 - 2 ^ 32 * x4) * (x1 - 2 ^ 32 * x5) - 2 ^ 32 * x6) - 2 ^ 32 * x7 →
    0 ≤ x2 + ((x3 - 2 ^ 32 * x4) * (x1 - 2 ^ 32 * x5) - 2 ^ 32 * x6) - 2 ^ 32 * x7 →
    x2 + ((x3 - 2 ^ 32 * x4) * (x1 - 2 ^ 32 * x5) - 2 ^ 32 * x6) - 2 ^ 32 * x7 < 2 ^ 32 →
    0 ≤ (x3 - 2 ^ 32 * x4) * (x1 - 2 ^ 32 * x5) - 2 ^ 32 * x6 →
    (x3 - 2 ^ 32 * x4) * (x1 - 2 ^ 32 * x5) - 2 ^ 32 * x6 < 2 ^ 32 →
    0 ≤ x1 - 2 ^ 32 * x5 →
    x1 - 2 ^ 32 * x5 < 2 ^ 32 →
    0 ≤ x3 - 2 ^ 32 * x4 →
    x3 - 2 ^ 32 * x4 < 2 ^ 32 →
    0 ≤ x2 →
    x2 < 2 ^ 32 → x3 * x1 < 2 ^ 32 →
    0 ≤ x3 →
    x2 + x3 * x1 < 2 ^ 32 → 8 ≤ x1 →
    x1 < 2 ^ 32 →
    False := by
  lia -verbose
