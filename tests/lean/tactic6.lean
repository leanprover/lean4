(* import("tactic.lua") *)
theorem T (a b c : Bool): a → b /\ c → c /\ a /\ b := _.
   conj_hyp
   apply and::intro
   (* Focus(Then(show_tac(), conj_tac(), show_tac(), assumption_tac()), 2) *)
   exact
   done

theorem T2 (a b c : Bool): a → b /\ c → c /\ a /\ b := _.
   conj_hyp
   apply and::intro
   (* show_tac() *)
   (* Focus(Then(show_tac(), conj_tac(), Focus(assumption_tac(), 1)), 2) *)
   (* show_tac() *)
   (* Focus(assumption_tac(), 1) *)
   (* show_tac() *)
   (* Focus(assumption_tac(), 1) *)
   done