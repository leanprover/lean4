set_option grind.warning false

example (x y : Int) :
    27 ≤ 11*x + 13*y →
    11*x + 13*y ≤ 45 →
    -10 ≤ 7*x - 9*y →
    7*x - 9*y ≤ 4 → False := by
  -- `omega` fails in this example
  grind

example (x : Int) : 100 ≤ x → x ≤ 10000 → 20000 ∣ 3*x → False := by
  grind
