def f (x : Nat) := x

#eval f 1

def g (x : String) : Nat := f (f x)

#eval g "hello"

def h (x : String) := g x + g x

#eval h "world"
