(* import("tactic.lua") *)
theorem T1 (a b : Bool) : a → b → a /\ b.
    apply and_intro.
    exact.
    done.
