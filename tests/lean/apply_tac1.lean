Import tactic.
Import int.

Variable f : Int -> Int -> Bool
Variable P : Int -> Int -> Bool
Axiom Ax1 (x y : Int) (H : P x y) : (f x y)
Theorem T1 (a : Int) : (P a a) => (f a a).
      apply Discharge.
      apply Ax1.
      exact.
      done.
Variable b : Int
Axiom Ax2 (x : Int) : (f x b)
(**
simple_tac = Repeat(OrElse(imp_tac(), assumption_tac(), apply_tac("Ax2"), apply_tac("Ax1")))
**)
Theorem T2 (a : Int) : (P a a) => (f a a).
     simple_tac.
     done.

Theorem T3 (a : Int) : (P a a) => (f a a).
     Repeat (OrElse (apply Discharge) exact (apply Ax2) (apply Ax1)).
     done.

Show Environment 2.