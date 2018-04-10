open expr tactic

example : true := by whnf (var 0) >> return ()

example : true := by whnf (app (var 0) (var 0)) >> return ()

example : true := by head_zeta (var 0) >> return ()

example : true := by unify (var 0) (var 0) >> return ()

example : true := by is_def_eq (var 0) (var 0) >> return ()

example (foo trivial) := by do
t ← infer_type (var 0),
to_expr ``(trivial) >>= apply
