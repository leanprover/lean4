import Int.
(*

-- Tactic for trying to prove goal using reflexivity, congruence and available assumptions
congr_tac = Try(unfold_tac("eq")) .. Repeat(OrElse(apply_tac("refl"), apply_tac("congr"), assumption_tac()))

*)

exit -- temporarily disable the following test

theorem T1 (a b : Int) (f : Int -> Int) : a = b -> (f (f a)) = (f (f b)) :=
   fun assumption : a = b,
      show (f (f a)) = (f (f b)), by congr_tac

print environment 1.
