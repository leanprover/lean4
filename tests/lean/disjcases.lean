(* import("tactic.lua") *)
variables a b c : Bool
axiom H : a \/ b
theorem T (a b : Bool) : a \/ b => b \/ a.
   apply Discharge.
   apply (DisjCases H).
   apply Disj2.
   exact.
   apply Disj1.
   exact.
   done.