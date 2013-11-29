(**
simple_tac = REPEAT(ORELSE(imp_tactic, conj_tactic)) .. assumption_tactic
**)

Theorem T4 (a b : Bool) : a => b => a /\ b /\ a := _.
        apply simple_tac
        done

Show Environment 1.