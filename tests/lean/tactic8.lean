(* import("tactic.lua") *)
Theorem T (a b : Bool) : a \/ b => (not b) => a := _.
     apply Discharge
     apply Discharge
     disj_hyp
     exact
     absurd
     done
Show Environment 1.