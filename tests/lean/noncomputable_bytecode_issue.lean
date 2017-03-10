constant a : nat

noncomputable meta def ex : tactic pexpr :=
return $ quote a

open tactic

run_cmd ex >>= to_expr >> return ()
