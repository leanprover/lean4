(* import("tactic.lua") *)
Definition f(a : Bool) : Bool := not a.

Theorem T (a b : Bool) : a \/ b => (f b) => a := _.
     apply Discharge
     apply Discharge
     disj_hyp
     unfold f
     exact
     absurd
     done

print Environment 1.