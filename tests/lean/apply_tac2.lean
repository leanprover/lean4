(* import("tactic.lua") *)
check @discharge
theorem T (a b : Bool) : a => b => b => a.
   apply discharge.
   apply discharge.
   apply discharge.
   exact.
   done.