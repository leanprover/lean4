Definition f(a : Bool) : Bool := not a.
Definition g(a b : Bool) : Bool := a \/ b.

Theorem T1 (a b : Bool) : (g a b) => (f b) => a := _.
     apply unfold_tactic
     apply imp_tactic
     apply imp_tactic
     apply disj_hyp_tactic
     apply assumption_tactic
     apply absurd_tactic
     done.

(**
simple_tac   = REPEAT(unfold_tactic) .. REPEAT(ORELSE(imp_tactic, conj_hyp_tactic, assumption_tactic, absurd_tactic, conj_hyp_tactic, disj_hyp_tactic))
**)

Definition h(a b : Bool) : Bool := g a b.

Theorem T2 (a b : Bool) : (h a b) => (f b) => a := _.
     apply simple_tac
     done.

Show Environment 1.
