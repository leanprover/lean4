(* import("tactic.lua") *)
Axiom magic (a : Bool) : a.

Theorem T (a : Bool) : a.
    apply magic.
    done.

print Environment 1.