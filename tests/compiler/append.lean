def main (xs : list string) : io unit :=
let ys1 := list.repeat 1 1000000 in
let ys2 := list.repeat 2 1000000 in
io.println (to_string (ys1 ++ ys2).length)
