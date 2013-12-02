Theorem T (a b : Bool) : ((fun x, x /\ b) a) => ((fun x, x) a).
   apply beta_tactic.
   apply imp_tactic.
   apply conj_hyp_tactic.
   apply assumption_tactic.
   done.

Variables p q : Bool.
Theorem T2 : p /\ q => q.
   apply imp_tactic.
   apply conj_hyp_tactic.
   apply assumption_tactic.
   done.