def f (x : Nat) := x + 1

@[deprecated f]
def g (x : Nat) := x + 1

#eval g 0 -- warning

set_option warningAsError true

#eval g 0 -- error
