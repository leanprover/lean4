
def ex1 (xs : List Nat) : Nat :=
xs.foldl (b := 0) fun sum x => sum + x

def f (a : Nat) (flag := true) : Nat :=
a + if flag then 1 else 0

def g (a : Nat) : Nat :=
f a (flg := false)
