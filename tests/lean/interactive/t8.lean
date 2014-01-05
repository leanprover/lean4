(* import("tactic.lua") *)
SetOption tactic::proof_state::goal_names true.
Theorem T (a : Bool) : a => a /\ a.
   apply Discharge.
   apply Conj.
   exact.
   done.
