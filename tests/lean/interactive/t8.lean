(* import("tactic.lua") *)
setoption tactic::proof_state::goal_names true.
theorem T (a : Bool) : a => a /\ a.
   apply discharge.
   apply and::intro.
   exact.
   done.
