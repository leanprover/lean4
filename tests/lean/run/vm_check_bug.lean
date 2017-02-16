def f : nat → nat → nat
| (x+1) (y+1) := f (x+100000000) y
| (x+1) 0     := x
| 0     (y+1) := 1
| 0     0     := 1

vm_eval f 1 1000
