open tactic expr
example : false := by do exact $ const `does_not_exist []
