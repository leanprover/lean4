def main (xs : List String) : IO Unit :=
let ys1 := List.replicate 1000000 1 in
let ys2 := List.replicate 1000000 2 in
IO.println (toString (ys1 ++ ys2).length)
