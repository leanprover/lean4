import Int.
(* import("tactic.lua") *)
variable f : Int -> Int -> Int

(*
refl_tac           = apply_tac("Refl")
congr_tac          = apply_tac("Congr")
symm_tac           = apply_tac("Symm")
trans_tac          = apply_tac("Trans")
unfold_homo_eq_tac = unfold_tac("eq")
auto = unfold_homo_eq_tac .. Repeat(OrElse(refl_tac, congr_tac, assumption_tac(), Then(symm_tac, assumption_tac(), now_tac())))
*)

theorem T1 (a b c : Int) (H1 : a = b) (H2 : a = c) : (f (f a a) b) = (f (f b c) a).
   auto.
   done.

theorem T2 (a b c : Int) (H1 : a = b) (H2 : a = c) : (f (f a c)) = (f (f b a)).
   auto.
   done.

print environment 2.