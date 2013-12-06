Set tactic::proof_state::goal_names true.
Theorem T (a : Bool) : a => a /\ a.
   apply imp_tac.
   apply Conj.
   assumption.
   done.
