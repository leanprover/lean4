(* import("tactic.lua") *)
theorem T (a b : Bool) : ((fun x, x /\ b) a) => ((fun x, x) a) := _ .
   beta.
   apply discharge.
   conj_hyp.
   exact.
   done.
