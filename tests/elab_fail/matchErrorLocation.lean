--

def head {α} (xs : List α) (h : xs = [] → False) : α :=
match (generalizing := false) he:xs with
| []   => h he
| x::_ => x
