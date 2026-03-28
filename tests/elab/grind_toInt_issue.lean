module
open Lean Grind

example (x : Fin 2) : ToInt.toInt x ≠ 0 → ToInt.toInt x ≠ 1 → False := by
  grind -ring

example (x : Fin 3) : x ≠ 1 → x ≠ 2 → x ≠ 0 → False := by
  grind -ring

example (x : Fin 3) : x ≠ 1 → x ≠ 2 → ToInt.toInt x ≠ 0 → False := by
  grind -ring

example (x : Fin 3) : ToInt.toInt x ≠ 0 → x ≠ 1 → x ≠ 2 → False := by
  grind -ring

example (x : Fin 3) : ToInt.toInt x ≠ 0 → ToInt.toInt x ≠ 1 → ToInt.toInt x ≠ 2 → False := by
  grind -ring

example (x y z : Fin 5) : ToInt.toInt (x + z) = ToInt.toInt y → z = 0 → x = y := by
  grind -ring

example (x y : Fin 5) : ToInt.toInt (x + 0) = ToInt.toInt y → x = y := by
  grind -ring
