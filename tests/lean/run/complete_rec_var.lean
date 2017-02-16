def f : nat → nat → nat
| (x+1) (y+1) := f (x+10) y
| _     _     := 1

vm_eval f 1 1000

example (x y) : f (x+1) (y+1) = f (x+10) y :=
rfl

example (y) : f 0 (y+1) = 1 :=
rfl

example (x) : f (x+1) 0  = 1 :=
rfl

example : f 0 0  = 1 :=
rfl
