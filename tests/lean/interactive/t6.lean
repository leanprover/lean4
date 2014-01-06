(* import("tactic.lua") *)
theorem T1 (a b : Bool) : a => b => a /\ b.
    (* imp_tac() *).
    (* imp_tac() *).
    apply and::intro.
    exact.
    done.
