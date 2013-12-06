Theorem T (a b : Bool) : ((fun x, x /\ b) a) => ((fun x, x) a) := _ .
   apply beta_tac.
   apply imp_tac.
   apply conj_hyp_tac.
   apply assumption_tac.
   done.
