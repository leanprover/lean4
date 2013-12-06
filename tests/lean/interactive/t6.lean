Theorem T1 (a b : Bool) : a => b => a /\ b.
    apply imp_tac.
    apply imp_tac.
    apply Conj.
    assumption.
    done.
