Theorem T1 (a b : Bool) : a => b => a /\ b.
    apply imp_tactic.
    apply imp_tactic.
    apply Conj.
    apply assumption_tactic.
    done.
