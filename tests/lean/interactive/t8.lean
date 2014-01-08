(* import("tactic.lua") *)
set::option tactic::proof_state::goal_names true.
theorem T (a : Bool) : a → a /\ a.
   apply and::intro.
   exact.
   done.
