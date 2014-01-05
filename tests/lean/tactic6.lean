(* import("tactic.lua") *)
Theorem T (a b c : Bool): a => b /\ c => c /\ a /\ b := _.
   apply Discharge
   apply Discharge
   conj_hyp
   apply Conj
   (* Focus(Then(show_tac(), conj_tac(), show_tac(), assumption_tac()), 2) *)
   exact
   done

Theorem T2 (a b c : Bool): a => b /\ c => c /\ a /\ b := _.
   apply Discharge
   apply Discharge
   conj_hyp
   apply Conj
   (* show_tac() *)
   (* Focus(Then(show_tac(), conj_tac(), Focus(assumption_tac(), 1)), 2) *)
   (* show_tac() *)
   (* Focus(assumption_tac(), 1) *)
   (* show_tac() *)
   (* Focus(assumption_tac(), 1) *)
   done