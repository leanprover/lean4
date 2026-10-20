module

/-!
The `Int` certificates of the `Sym.Arith` normalizer (`Init.Grind.Ring.IntSolver`) are checked by
the kernel by evaluation, so the certificate checkers must be exposed: in a `module` file, the
proofs below were rejected with `(kernel) application type mismatch`.
-/

set_option warn.sorry false

variable (x y : Int)

example : 2 * x < 11 := by grind_norm sym; guard_target = (x + -5 ≤ 0); sorry
example : 2 * x + 2 ≤ 0 := by grind_norm sym; guard_target = (x + 1 ≤ 0); sorry
example : 3 * x = 6 := by grind_norm sym; guard_target = (x = 2); sorry
example : 2 * x + 4 * y = 5 := by grind_norm sym; guard_target = False; sorry
example : (6 : Int) ∣ 4 * x + 2 := by grind_norm sym; guard_target = ((3 : Int) ∣ 2 * x + 1); sorry
example : (4 : Int) ∣ 2 * x + 1 := by grind_norm sym; guard_target = False; sorry
