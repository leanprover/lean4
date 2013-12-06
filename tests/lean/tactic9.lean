Definition f(a : Bool) : Bool := not a.

Theorem T (a b : Bool) : a \/ b => (f b) => a := _.
     apply imp_tac
     apply imp_tac
     apply disj_hyp_tac
     apply (** unfold_tac("f") **)
     apply assumption_tac
     apply absurd_tac
     done
Show Environment 1.