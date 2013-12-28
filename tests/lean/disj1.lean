Import tactic

Theorem T1 (a b : Bool) : a \/ b => b \/ a.
    apply Discharge.
    (** disj_hyp_tac() **)
    (** disj_tac() **)
    back
    exact.
    (** disj_tac() **)
    exact.
    done.

(**
simple_tac = Repeat(OrElse(imp_tac(), assumption_tac(), disj_hyp_tac(), disj_tac())) .. now_tac()
**)

Theorem T2 (a b : Bool) : a \/ b => b \/ a.
    simple_tac.
    done.

Show Environment 1.