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
      id
        (h_1
          (CommRing.eq_normS (RArray.branch 1 (RArray.leaf a) (RArray.leaf b))
            (((CommRing.Expr.var 0).add (CommRing.Expr.var 1)).pow 2)
            ((((CommRing.Expr.var 0).pow 2).add
                  (((CommRing.Expr.num 2).mul (CommRing.Expr.var 0)).mul (CommRing.Expr.var 1))).add
              ((CommRing.Expr.var 1).pow 2))
            (eagerReduce (Eq.refl true))))
-/
#guard_msgs in -- context should contain only `a` and `b`
set_option trace.grind.debug.proof true in
example (a b c d : R) : c + d = d → (a + b)^2 ≠ a^2 + 2 * a * b + b^2 → False := by grind

end CommSemiring
