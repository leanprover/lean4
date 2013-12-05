Theorem T1 (a b : Bool) : a \/ b => b \/ a.
    apply imp_tactic
    apply disj_hyp_tactic
    apply disj_tactic
    back
    apply assumption_tactic
    apply disj_tactic
    apply assumption_tactic
    done

(**
simple_tac = REPEAT(ORELSE(imp_tactic, assumption_tactic, disj_hyp_tactic, disj_tactic)) .. now_tactic
**)

Theorem T2 (a b : Bool) : a \/ b => b \/ a.
    apply simple_tac
    done

Show Environment 1.