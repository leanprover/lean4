Theorem T (a b c : Bool): a => b /\ c => c /\ a /\ b := _.
   apply imp_tac
   apply imp_tac
   apply conj_hyp_tac
   apply conj_tac
   apply (** FOCUS(THEN(show_tac, conj_tac, show_tac, assumption_tac), 2) **)
   apply assumption_tac
   done

Theorem T2 (a b c : Bool): a => b /\ c => c /\ a /\ b := _.
   apply imp_tac
   apply imp_tac
   apply conj_hyp_tac
   apply conj_tac
   apply show_tac
   apply (** FOCUS(THEN(show_tac, conj_tac, FOCUS(assumption_tac, 1)), 2) **)
   apply show_tac
   apply (** FOCUS(assumption_tac, 1) **)
   apply show_tac
   apply (** FOCUS(assumption_tac, 1) **)
   done