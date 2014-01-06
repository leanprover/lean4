import tactic.
import Int.

variable f : Int -> Int -> Bool
variable P : Int -> Int -> Bool
axiom Ax1 (x y : Int) (H : P x y) : (f x y)
theorem T1 (a : Int) : (P a a) => (f a a).
      apply discharge.
      apply Ax1.
      exact.
      done.
variable b : Int
axiom Ax2 (x : Int) : (f x b)
(*
simple_tac = Repeat(OrElse(imp_tac(), assumption_tac(), apply_tac("Ax2"), apply_tac("Ax1")))
*)
theorem T2 (a : Int) : (P a a) => (f a a).
     simple_tac.
     done.

theorem T3 (a : Int) : (P a a) => (f a a).
     Repeat (OrElse (apply discharge) exact (apply Ax2) (apply Ax1)).
     done.

print environment 2.