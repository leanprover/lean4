(* import("tactic.lua") *)
Definition f(a : Bool) : Bool := not a.
Definition g(a b : Bool) : Bool := a \/ b.

Theorem T1 (a b : Bool) : (g a b) => (f b) => a := _.
     unfold_all
     apply Discharge
     apply Discharge
     disj_hyp
     exact
     absurd
     done.

(*
simple_tac   = Repeat(unfold_tac()) .. Repeat(OrElse(imp_tac(), conj_hyp_tac(), assumption_tac(), absurd_tac(), conj_hyp_tac(), disj_hyp_tac()))
*)

Definition h(a b : Bool) : Bool := g a b.

Theorem T2 (a b : Bool) : (h a b) => (f b) => a := _.
     simple_tac
     done.

print Environment 1.
