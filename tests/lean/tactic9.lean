Definition f(a : Bool) : Bool := not a.

Theorem T (a b : Bool) : a \/ b => (f b) => a := _.
     apply imp_tactic
     apply imp_tactic
     apply disj_hyp_tactic
     apply (** unfold_tactic("f") **)
     apply assumption_tactic
     apply absurd_tactic
     done
Show Environment 1.