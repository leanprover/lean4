(* import("tactic.lua") *)
theorem T (a b : Bool) : ((fun x, x /\ b) a) → ((fun x, x) a).
   beta.
   conj_hyp.
   exact.
   done.

variables p q : Bool.
theorem T2 : p /\ q → q.
   conj_hyp.
   exact.
   done.