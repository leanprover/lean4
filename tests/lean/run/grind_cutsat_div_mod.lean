set_option grind.warning false

example (x y : Int) : x / 2 + y = 3 → x = 5 → y = 1 := by
  grind

example (x y : Int) : x / -2 + y = 3 → x = 5 → y = 5 := by
  grind

example (x y : Int) : x % -2 + y = 3 → x = 5 → y = 2 := by
  grind

example (x y : Int) : x % 2 + y = 3 → x = 5 → y = 2 := by
  grind

/--
info: [grind.cutsat.model] x := 5
[grind.cutsat.model] y := 2
-/
#guard_msgs (info) in
set_option trace.grind.cutsat.model true in
example (x y : Int) : x % 2 + y = 3 → x ≤ 5 → x > 4 → y = 1 := by
  fail_if_success grind
  sorry

example (x y : Int) : x = y / 2 → y % 2 = 0 → y - 2*x = 0 := by
  grind

example (x : Int) : x ≥ 0 → (x + 4) / 2 ≤ x + 2 := by
  grind
