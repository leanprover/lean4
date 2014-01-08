(* import("tactic.lua") *)
definition f(a : Bool) : Bool := not a.
definition g(a b : Bool) : Bool := a \/ b.

theorem T1 (a b : Bool) : (g a b) → (f b) → a := _.
     unfold_all
     disj_hyp
     exact
     absurd
     done.

(*
simple_tac   = Repeat(unfold_tac()) .. Repeat(OrElse(conj_hyp_tac(), assumption_tac(), absurd_tac(), conj_hyp_tac(), disj_hyp_tac()))
*)

definition h(a b : Bool) : Bool := g a b.

theorem T2 (a b : Bool) : (h a b) → (f b) → a := _.
     simple_tac
     done.

print environment 1.
