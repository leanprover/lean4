Theorem T (a b : Bool) : ((fun x, x /\ b) a) => ((fun x, x) a) := _ .
   apply beta_tactic.
   apply imp_tactic.
   apply conj_hyp_tactic.
   apply assumption_tactic.
   done.
