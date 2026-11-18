/-!
Equations `x + -1 * y = 0` and `x + k = 0` are normalized to `x = y` and `x = -k` by both `grind`
normalizers and by `simp +arith`. These rules used to be shadowed by the check for an equation
already of the form `p = 0`, so they fired only when the input was not in that form yet.
-/

set_option warn.sorry false

variable (x y : Int)

example : x + -1 * y = 0 := by grind_norm; guard_target =ₛ x = y; sorry
example : x + -1 * y = 0 := by grind_norm sym; guard_target =ₛ x = y; sorry
example : x + 2 = 0 := by grind_norm; guard_target =ₛ x = -2; sorry
example : x + 2 = 0 := by grind_norm sym; guard_target =ₛ x = -2; sorry
example : x + -2 = 0 := by grind_norm; guard_target =ₛ x = 2; sorry
example : x + -2 = 0 := by grind_norm sym; guard_target =ₛ x = 2; sorry

-- The rules already applied to inputs not of the form `p = 0`.
example : 2 * x = 2 * y := by grind_norm; guard_target =ₛ x = y; sorry
example : 2 * x = 2 * y := by grind_norm sym; guard_target =ₛ x = y; sorry
example : 2 * x = 4 := by grind_norm; guard_target =ₛ x = 2; sorry
example : 2 * x = 4 := by grind_norm sym; guard_target =ₛ x = 2; sorry

-- Both normalizers agree.
#guard_msgs in
example : x + -1 * y = 0 := by grind_norm check; sorry
-- Accepted difference: the legacy normalizer has a certificate theorem (`norm_eq_var`) only for
-- the variable order `x + -1 * y`, so it leaves `-1 * x + y = 0` alone, while Sym writes `y = x`.
/--
error: `grind_norm` discrepancy
legacy:
  -1 * x + y = 0
sym:
  y = x
-/
#guard_msgs in
example : -1 * x + y = 0 := by grind_norm check; sorry
#guard_msgs in
example : x + 2 = 0 := by grind_norm check; sorry
#guard_msgs in
example : x + -1 * y + 3 = 0 := by grind_norm check; sorry

example : x + -1 * y = 0 ↔ x = y := by simp +arith
example : x + 2 = 0 ↔ x = -2 := by simp +arith
example : x + -2 = 0 ↔ x = 2 := by simp +arith
