(* import("tactic.lua") *)
variables a b c : Bool
axiom H : a \/ b
theorem T (a b : Bool) : a \/ b → b \/ a.
   apply (or_elim H).
   apply or_intror.
   exact.
   apply or_introl.
   exact.
   done.