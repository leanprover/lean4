Theorem T (a b : Bool) : a \/ b => (not b) => a := _.
     apply imp_tac
     apply imp_tac
     apply disj_hyp_tac
     apply assumption_tac
     apply absurd_tac
     done
Show Environment 1.