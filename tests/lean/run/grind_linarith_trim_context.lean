module
/--
trace: [grind.debug.proof] fun h h_1 h_2 h_3 h_4 h_5 h_6 h_7 h_8 =>
      let ctx := RArray.branch 1 (RArray.leaf One.one) (RArray.leaf (f 2));
      let p_1 := Poly.nil;
      let p_2 := Poly.add 1 1 Poly.nil;
      let p_3 := Poly.add 1 0 Poly.nil;
      let p_4 := Poly.add (-1) 1 (Poly.add 1 0 Poly.nil);
      let p_5 := Poly.add (-1) 0 Poly.nil;
      let e_1 := (Expr.intMul 1 (Expr.var 1)).add (Expr.intMul 0 (Expr.var 0));
      let e_2 := Expr.zero;
      let e_3 := (Expr.intMul (-1) (Expr.var 1)).add (Expr.intMul 1 (Expr.var 0));
      let rctx := RArray.leaf (f 2);
      let rp_1 := CommRing.Poly.add 1 (CommRing.Mon.mult { x := 0, k := 1 } CommRing.Mon.unit) (CommRing.Poly.num 0);
      let rp_2 := CommRing.Poly.add (-1) (CommRing.Mon.mult { x := 0, k := 1 } CommRing.Mon.unit) (CommRing.Poly.num 1);
      let re_1 := CommRing.Expr.var 0;
      let re_2 := CommRing.Expr.num 0;
      let re_3 := ((CommRing.Expr.num 1).neg.mul (CommRing.Expr.var 0)).add (CommRing.Expr.num 1);
      lt_unsat ctx
        (le_lt_combine ctx p_3 p_5 p_1 (eagerReduce (Eq.refl true))
          (le_le_combine ctx p_4 p_2 p_3 (eagerReduce (Eq.refl true))
            (le_norm ctx e_3 e_2 p_4 (eagerReduce (Eq.refl true))
              (CommRing.le_norm rctx re_3 re_2 rp_2 (eagerReduce (Eq.refl true)) h_8))
            (le_norm ctx e_1 e_2 p_2 (eagerReduce (Eq.refl true))
              (CommRing.le_norm rctx re_1 re_2 rp_1 (eagerReduce (Eq.refl true)) h_1)))
          (zero_lt_one ctx p_5 (eagerReduce (Eq.refl true)) (Eq.refl One.one)))
-/
#guard_msgs in
open Std Lean Grind Linarith in
set_option trace.grind.debug.proof true in -- Context should contain only `f 2` and `One`
example [CommRing α] [LE α] [LT α] [LawfulOrderLT α] [IsLinearOrder α] [OrderedRing α] (f : Nat → α) :
    f 1 <= 0 → f 2 <= 0 → f 3 <= 0 → f 4 <= 0 → f 5 <= 0 → f 6 <= 0 → f 7 <= 0 → f 8 <= 0 → -1 * f 2 + 1 <= 0 → False := by
  grind
