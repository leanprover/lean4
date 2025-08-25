module
open Lean.Grind

-- `grind linarith` currently does not support negation of linear constraints.
variable (R : Type u) [IntModule R] [LE R] [LT R] [Preorder R] [OrderedAdd R]

example (a b : R) (_ : a < b) (_ : b < a) : False := by grind
example (a b : R) (_ : a < b ∧ b < a) : False := by grind
example (a b : R) (_ : a < b) : a ≠ b := by grind

example (x y z : Int) (h1 : 2 * x < 3 * y) (h2 : -4 * x + 2 * z < 0) (h3 : 12 * y - 4 * z < 0) : False := by
  grind
example (x y z : R) (h1 : 2 • x < 3 • y) (h2 : -4 • x + 2 • z < 0) (h3 : 12 • y - 4 • z < 0) : False := by
  grind

example (x y z : Int) (h1 : 2 * x < 3 * y) (h2 : -4 * x + 2 * z < 0) (h3 : x * y < 5) (h3 : 12 * y - 4 * z < 0) :
    False := by grind
example (x y z : R) (h1 : 2 • x < 3 • y) (h2 : -4 • x + 2 • z < 0) (h3 : 12 • y - 4 • z < 0) :
    False := by grind

-- It does cancel the double negation in the following two examples
example (x y z : Int) (h1 : 2 * x < 3 * y) (h2 : -4 * x + 2 * z < 0) (h3 : x * y < 5) : ¬ 12 * y - 4 * z < 0 := by
  grind
example (x y z : R) (h1 : 2 • x < 3 • y) (h2 : -4 • x + 2 • z < 0) : ¬ 12 • y - 4 • z < 0 := by
  grind
