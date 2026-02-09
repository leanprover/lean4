module
example (x : BitVec 2) : x - 2 • x + x = 0 := by
  grind

example (x : BitVec 2) : x + (-2) • x + x = 0 := by
  grind

example (x : Fin 7) : x + (-2) • x + x = 0 := by
  grind

example (x : Int) : x + (-2) • x + x = 0 := by
  grind

example (x : Int) : x - 2 • x + x = 0 := by
  grind
