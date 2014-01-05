(* import("tactic.lua") *)
axiom magic (a : Bool) : a.

theorem T (a : Bool) : a.
    apply magic.
    done.

print environment 1.