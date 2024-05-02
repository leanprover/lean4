
def f (x y : Nat) (h : x = y := by assumption) : Nat :=
x + x

def g (x y z : Nat) (h : x = y) : Nat :=
f x y

def f2 (x y : Nat) (h : x = y := by exact rfl) : Nat :=
x + x

def f3 (x y : Nat) (h : x = y := by exact Eq.refl x) : Nat :=
x + x

#check fun x => f2 x x
#check fun x => f3 x x
