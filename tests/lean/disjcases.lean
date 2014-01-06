(* import("tactic.lua") *)
variables a b c : Bool
axiom H : a \/ b
theorem T (a b : Bool) : a \/ b => b \/ a.
   apply discharge.
   apply (or::elim H).
   apply or::intror.
   exact.
   apply or::introl.
   exact.
   done.