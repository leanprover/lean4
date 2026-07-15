def g (xs ys : List Nat) (a : α) : IO Nat := do
  let mut sum := 0
  for x in xs, y in ys, c in a, z in ys do
    sum := x + sum
    IO.println s!"x: {x}, y: {y}, a: {a}, c: {c}, sum: {sum}"
  return sum
