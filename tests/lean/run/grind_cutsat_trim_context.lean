module
/--
trace: [grind.debug.proof] fun h h_1 h_2 h_3 h_4 h_5 h_6 h_7 h_8 =>
      id
        (let ctx := RArray.leaf (f 2);
        let p_1 := Poly.add 1 0 (Poly.num 0);
        let p_2 := Poly.add (-1) 0 (Poly.num 1);
        let p_3 := Poly.num 1;
        le_unsat ctx p_3 (eagerReduce (Eq.refl true)) (le_combine ctx p_2 p_1 p_3 (eagerReduce (Eq.refl true)) h_8 h_1))
-/
#guard_msgs in -- `cutsat` context should contain only `f 2`
open Lean Int Linear in
set_option trace.grind.debug.proof true in
example (f : Nat → Int) :
    f 1 <= 0 → f 2 <= 0 → f 3 <= 0 → f 4 <= 0 → f 5 <= 0 → f 6 <= 0 → f 7 <= 0 → f 8 <= 0 → -1 * f 2 + 1 <= 0 → False := by
  grind -order
