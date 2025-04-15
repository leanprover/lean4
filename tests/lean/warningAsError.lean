set_option linter.deprecated true

def f (x : Nat) := x + 1

@[deprecated f (since := "1970-01-01")]
def g (x : Nat) := x + 1

#eval g 0 -- warning

set_option warningAsError true

#eval g 0 -- error

set_option linter.unusedVariables true
def h (unused : Nat) := 0  -- error
