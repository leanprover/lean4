
def f : Nat → Nat → Nat
| 0,   b => b+1
| a+1, b => f a (f a b)

theorem ex1 (b)   : f 0 b = b+1 := rfl
theorem ex2 (b)   : f 1 b = (b+1)+1 := rfl
theorem ex3 (b)   : f 2 b = b+1+1+1+1 := rfl
theorem ex4 (a b) : f (a+1) b = f a (f a b) := rfl

#eval f 2 5
