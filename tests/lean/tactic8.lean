Theorem T (a b : Bool) : a \/ b => (not b) => a := _.
     apply imp_tactic
     apply imp_tactic
     apply disj_hyp_tactic
     apply assumption_tactic
     apply absurd_tactic
     done
Show Environment 1.