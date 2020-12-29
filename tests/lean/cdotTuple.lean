#eval [1, 2, 3].map (·, 1)

#eval (·, ·) 1 2

#eval (., ., .) 1 2 3

theorem ex1 : [1, 2, 3].map (·, 1) = [(1, 1), (2, 1), (3, 1)] :=
  rfl

theorem ex2 : (., .) 1 2 = (1, 2) :=
  rfl
