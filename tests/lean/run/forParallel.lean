-- set_option trace.Elab true
def f (xs : Array Nat) (ys : List (Nat × Nat)) (s : String) : IO Unit := do
  for x in xs, (y₁, y₂) in ys, c in s do
    IO.println s!"x: {x}, y₁: {y₁}, y₂: {y₂}, c: {c}"

/--
info: x: 1, y₁: 5, y₂: 15, c: h
x: 2, y₁: 6, y₂: 16, c: e
x: 3, y₁: 7, y₂: 17, c: l
-/
#guard_msgs in
#eval f #[1, 2, 3, 4] [(5, 15), (6, 16), (7, 17)] "hello"
