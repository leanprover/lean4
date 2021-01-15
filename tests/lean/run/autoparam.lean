
def f (x y : Nat) (h : x = y := by assumption) : Nat :=
x + x

def g (x y z : Nat) (h : x = y) : Nat :=
f x y
