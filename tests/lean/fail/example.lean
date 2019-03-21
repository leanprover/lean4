open tactic Expr
example : False := by do exact $ const `doesNotExist []
