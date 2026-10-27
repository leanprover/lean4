module
/--
trace: [grind.debug.proof] fun h h_1 h_2 h_3 =>
      Classical.byContradiction fun h_4 =>
        id
          (let ctx := RArray.branch 1 (RArray.leaf x) (RArray.leaf x⁻¹);
          let e_1 := (Expr.var 0).mul (Expr.var 1);
          let e_2 := Expr.num (Int.ofNat 0);
          let e_3 := Expr.num (Int.ofNat 1);
          let e_4 := (Expr.var 0).pow 2;
          let m_1 := Mon.mult (Power.mk 1 1) Mon.unit;
          let m_2 := Mon.mult (Power.mk 0 1) Mon.unit;
          let p_1 := Poly.num (Int.negSucc 0);
          let p_2 := Poly.add (Int.negSucc 0) (Mon.mult (Power.mk 0 1) Mon.unit) (Poly.num (Int.ofNat 0));
          let p_3 := Poly.add (Int.ofNat 1) (Mon.mult (Power.mk 0 2) Mon.unit) (Poly.num (Int.ofNat 0));
          let p_4 :=
            Poly.add (Int.ofNat 1) (Mon.mult (Power.mk 0 1) (Mon.mult (Power.mk 1 1) Mon.unit))
              (Poly.num (Int.negSucc 0));
          let p_5 := Poly.add (Int.ofNat 1) (Mon.mult (Power.mk 0 1) Mon.unit) (Poly.num (Int.ofNat 0));
          one_eq_zero_unsat ctx p_1 (eagerReduce (Eq.refl true))
            (Stepwise.simp1 ctx p_4 (-1) m_1 p_5 p_1 [1] (Eq.refl p_1)
              (Stepwise.core ctx e_1 e_3 p_4 (Eq.refl p_4) (diseq0_to_eq x h_4))
              (Stepwise.mul ctx p_2 (-1) p_5 (eagerReduce (Eq.refl true))
                (Stepwise.superpose ctx 1 m_2 p_4 (-1) m_1 p_3 p_2 [1] (Eq.refl p_2)
                  (Stepwise.core ctx e_1 e_3 p_4 (Eq.refl p_4) (diseq0_to_eq x h_4))
                  (Stepwise.core ctx e_4 e_2 p_3 (Eq.refl p_3) h)))))
-/
#guard_msgs in -- Context should contains only `x` and its inverse.
set_option trace.grind.debug.proof true in
set_option pp.structureInstances false in
open Lean Grind CommRing in
example [Field α] (x y z w : α) :
   x^2 = 0 → y^2 = 0 → z^3 = 0 → w^2 = 0 → x = 0 := by
  grind
