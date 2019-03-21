def main (xs : List String) : IO Unit :=
let ys1 := List.repeat 1 1000000 in
let ys2 := List.repeat 2 1000000 in
IO.println (toString (ys1 ++ ys2).length)
