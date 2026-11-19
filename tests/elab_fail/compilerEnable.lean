/-!
Tests `compiler.enable`: declarations elaborated while it is disabled are not compiled and thus
cannot be run.
-/

set_option compiler.enable false in
def f (x : Nat) : Nat := x + 1

def g (x : Nat) : Nat := x + 1

#eval g 1

#eval f 1

def h (x : Nat) : Nat := f x

set_option compiler.enable false

def g' (x : Nat) : Nat := g x

#eval g 1

set_option compiler.enable true

#eval g 1

#eval g' 1
