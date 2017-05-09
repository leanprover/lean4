constant a : nat

noncomputable meta def ex : tactic expr :=
return ```(a)

open tactic

run_cmd ex >> return ()
