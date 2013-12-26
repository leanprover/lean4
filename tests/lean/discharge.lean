(** import("tactic.lua") **)
Check @Discharge
Theorem T (a b : Bool) : a => b => b => a.
   apply Discharge.
   apply Discharge.
   apply Discharge.
   exact.
   done.