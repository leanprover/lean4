module
open Lean Grind

section CommSemiring

variable (R : Type u) [CommSemiring R]

example (a b c : R) : a * (b + c) = a * c + b * a := by grind
example (a b : R) : (a + b)^2 = a^2 + 2 * a * b + b^2 := by grind
example (a b : R) : (a + 2 * b)^2 = a^2 + 4 * a * b + 4 * b^2 := by grind
example (a b : R) : (a + 2 * b)^2 = 4 * b^2 + b * 4 * a + a^2 := by grind

example (a b : R) : (a + b)^2 ≠ a^2 + 2 * a * b + b^2 → False := by grind

/--
trace: [grind.debug.proof] fun h h_1 =>
      h_1
        (Ring.OfSemiring.eq_normS (RArray.branch 1 (RArray.leaf a) (RArray.leaf b))
          (((Ring.OfSemiring.Expr.var 0).add (Ring.OfSemiring.Expr.var 1)).pow 2)
          ((((Ring.OfSemiring.Expr.var 0).pow 2).add
                (((Ring.OfSemiring.Expr.num 2).mul (Ring.OfSemiring.Expr.var 0)).mul (Ring.OfSemiring.Expr.var 1))).add
            ((Ring.OfSemiring.Expr.var 1).pow 2))
          (eagerReduce (Eq.refl true)))
-/
#guard_msgs in -- context should contain only `a` and `b`
set_option trace.grind.debug.proof true in
example (a b c d : R) : c + d = d → (a + b)^2 ≠ a^2 + 2 * a * b + b^2 → False := by grind

end CommSemiring
