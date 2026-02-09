

macro "foo!" x:term : term => `(let xs := $x; xs.succ + xs)

def f1 (x : Nat) : Nat :=
foo! x+1

theorem ex1 (x : Nat) : f1 x = Nat.succ (x+1) + (x + 1) :=
rfl

def f2 (xs : Nat) : Nat :=
foo! xs

theorem ex2 (x : Nat) : f2 x = Nat.succ x + x :=
rfl
