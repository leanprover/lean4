

def head {α} (xs : List α) (h : xs = [] → False) : α :=
match he:xs with
| []   => h he
| x::_ => x
