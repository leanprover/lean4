Definition f(a : Bool) : Bool := not a.
Definition g(a b : Bool) : Bool := a \/ b.

Theorem T1 (a b : Bool) : (g a b) => (f b) => a := _.
     apply unfold_tac
     apply imp_tac
     apply imp_tac
     apply disj_hyp_tac
     assumption
     apply absurd_tac
     done.

(**
simple_tac   = REPEAT(unfold_tac) .. REPEAT(ORELSE(imp_tac, conj_hyp_tac, assumption_tac, absurd_tac, conj_hyp_tac, disj_hyp_tac))
**)

Definition h(a b : Bool) : Bool := g a b.

Theorem T2 (a b : Bool) : (h a b) => (f b) => a := _.
     apply simple_tac
     done.

Show Environment 1.
