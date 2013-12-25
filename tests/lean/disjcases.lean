Variables a b c : Bool
Axiom H : a \/ b
Theorem T (a b : Bool) : a \/ b => b \/ a.
   apply Discharge.
   apply (DisjCases H).
   apply Disj2.
   assumption.
   apply Disj1.
   assumption.
   done.