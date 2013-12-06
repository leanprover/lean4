(**
simple_tac = REPEAT(ORELSE(imp_tac, conj_tac)) .. assumption_tac
**)

Theorem T4 (a b : Bool) : a => b => a /\ b /\ a := _.
        apply simple_tac
        done

Show Environment 1.