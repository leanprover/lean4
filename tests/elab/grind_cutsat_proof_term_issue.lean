example (x y : UInt8) : 3*x = 1 → 3*y = 2 → x + y = 1 := by
  grind -ring -ac -linarith

example (x y : Fin 11) : 3*x = 1 → 3*y = 2 → x + y = 1 := by
  grind -ring  -ac -linarith
