example {a b : Nat} (ha : 1 ≤ a) : (a - 1 + 1) * b = a * b := by grind

/--
info: Try this:
  [apply] ⏎
    mbtc
    cases #9501
-/
#guard_msgs in
example {a b : Nat} (ha : 1 ≤ a) : (a - 1 + 1) * b = a * b := by
  grind => finish? -- mbtc was applied consider nonlinear `*`
