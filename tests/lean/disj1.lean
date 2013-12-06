Theorem T1 (a b : Bool) : a \/ b => b \/ a.
    apply imp_tac
    apply disj_hyp_tac
    apply disj_tac
    back
    apply assumption_tac
    apply disj_tac
    apply assumption_tac
    done

(**
simple_tac = REPEAT(ORELSE(imp_tac, assumption_tac, disj_hyp_tac, disj_tac)) .. now_tac
**)

Theorem T2 (a b : Bool) : a \/ b => b \/ a.
    apply simple_tac
    done

Show Environment 1.