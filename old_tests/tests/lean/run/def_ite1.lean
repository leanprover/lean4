
definition f : nat → nat → nat
| 100 2 := 0
| _   4 := 1
| _   _ := 2

example : f 100 2 = 0 := rfl
example : f 9 4   = 1 := rfl
example : f 8 4   = 1 := rfl
example : f 6 3   = 2 := rfl
