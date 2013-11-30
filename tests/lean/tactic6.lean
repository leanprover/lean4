Theorem T (a b c : Bool): a => b /\ c => c /\ a /\ b := _.
   apply imp_tactic
   apply imp_tactic
   apply conj_hyp_tactic
   apply conj_tactic
   apply (** FOCUS(THEN(show_tactic, conj_tactic, show_tactic, assumption_tactic), 2) **)
   apply assumption_tactic
   done

Theorem T2 (a b c : Bool): a => b /\ c => c /\ a /\ b := _.
   apply imp_tactic
   apply imp_tactic
   apply conj_hyp_tactic
   apply conj_tactic
   apply show_tactic
   apply (** FOCUS(THEN(show_tactic, conj_tactic, FOCUS(assumption_tactic, 1)), 2) **)
   apply show_tactic
   apply (** FOCUS(assumption_tactic, 1) **)
   apply show_tactic
   apply (** FOCUS(assumption_tactic, 1) **)
   done