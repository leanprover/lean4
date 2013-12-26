(** import("tactic.lua") **)
Axiom magic (a : Bool) : a.

Theorem T (a : Bool) : a.
    apply magic.
    done.

Show Environment 1.