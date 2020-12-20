-- set_option trace.Elab true
def f (xs : Array Nat) (ys : List (Nat × Nat)) (s : String) : IO Unit := do
  for x in xs, (y₁, y₂) in ys, c in s do
    IO.println s!"x: {x}, y₁: {y₁}, y₂: {y₂}, c: {c}"

#eval f #[1, 2, 3, 4] [(5, 15), (6, 16), (7, 17)] "hello"
