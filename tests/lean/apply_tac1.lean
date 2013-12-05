Variable f : Int -> Int -> Bool
Variable P : Int -> Int -> Bool
Axiom Ax1 (x y : Int) (H : P x y) : (f x y)
Theorem T1 (a : Int) : (P a a) => (f a a).
      apply imp_tactic
      apply (** apply_tactic("Ax1") **)
      apply assumption_tactic
      done
Variable b : Int
Axiom Ax2 (x : Int) : (f x b)
(**
simple_tac = REPEAT(ORELSE(imp_tactic, assumption_tactic, apply_tactic("Ax2"), apply_tactic("Ax1")))
**)
Theorem T2 (a : Int) : (P a a) => (f a a).
     apply simple_tac
     done

Show Environment 1.