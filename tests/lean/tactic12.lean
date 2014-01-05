(* import("tactic.lua") *)
Theorem T (a b : Bool) : ((fun x, x /\ b) a) => ((fun x, x) a).
   beta.
   apply Discharge.
   conj_hyp.
   exact.
   done.

Variables p q : Bool.
Theorem T2 : p /\ q => q.
   apply Discharge.
   conj_hyp.
   exact.
   done.