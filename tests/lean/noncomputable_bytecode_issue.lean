constant a : nat

meta def ex : tactic expr :=
return `(a)

open tactic

run_cmd ex >> return ()
