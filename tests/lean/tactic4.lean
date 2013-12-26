(**
simple_tac = Repeat(OrElse(imp_tac(), conj_tac())) .. assumption_tac()
**)

Theorem T4 (a b : Bool) : a => b => a /\ b := _.
        simple_tac
        done

Show Environment 1.