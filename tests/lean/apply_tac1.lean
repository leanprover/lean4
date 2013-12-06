Variable f : Int -> Int -> Bool
Variable P : Int -> Int -> Bool
Axiom Ax1 (x y : Int) (H : P x y) : (f x y)
Theorem T1 (a : Int) : (P a a) => (f a a).
      apply (** imp_tac **)
      apply (Ax1)
      assumption
      done
Variable b : Int
Axiom Ax2 (x : Int) : (f x b)
(**
simple_tac = REPEAT(ORELSE(imp_tac, assumption_tac, apply_tac("Ax2"), apply_tac("Ax1")))
**)
Theorem T2 (a : Int) : (P a a) => (f a a).
     apply simple_tac
     done

Show Environment 1.