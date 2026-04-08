

def main (xs : List String) : IO Unit :=
let ys1 := List.replicate 1000000 1;
let ys2 := List.replicate 1000000 2;
IO.println (toString (ys1 ++ ys2).length)
