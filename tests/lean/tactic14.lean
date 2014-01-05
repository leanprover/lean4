import Int.
(*

-- Tactic for trying to prove goal using Reflexivity, Congruence and available assumptions
congr_tac = Try(unfold_tac("eq")) .. Repeat(OrElse(apply_tac("Refl"), apply_tac("Congr"), assumption_tac()))

*)

theorem T1 (a b : Int) (f : Int -> Int) : a = b -> (f (f a)) = (f (f b)) :=
   fun assumption : a = b,
      have (f (f a)) = (f (f b)) by congr_tac

print environment 1.
