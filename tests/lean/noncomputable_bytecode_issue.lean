constant a : nat

noncomputable meta def ex : tactic pexpr :=
return $ quote a

open tactic

run_command ex >>= to_expr >> return ()
