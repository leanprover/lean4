(* import("tactic.lua") *)
set_option tactic::proof_state::goal_names true.
theorem T (a : Bool) : a → a /\ a.
   apply and_intro.
   exact.
   done.
