(* import("tactic.lua") *)
definition f(a : Bool) : Bool := not a.

theorem T (a b : Bool) : a \/ b => (f b) => a := _.
     apply Discharge
     apply Discharge
     disj_hyp
     unfold f
     exact
     absurd
     done

print environment 1.