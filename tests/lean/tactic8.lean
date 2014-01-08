(* import("tactic.lua") *)
theorem T (a b : Bool) : a \/ b → (not b) → a := _.
     disj_hyp
     exact
     absurd
     done
print environment 1.