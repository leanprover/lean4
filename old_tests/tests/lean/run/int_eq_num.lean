def f : int → nat
| -100 := 0
| 0    := 1
| 3    := 2
| _    := 4

#eval f (-100)
#eval f 0
#eval f 3
#eval f 5
