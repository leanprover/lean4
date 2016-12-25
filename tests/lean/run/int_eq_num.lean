def f : int → nat
| -100 := 0
| 0    := 1
| 3    := 2
| _    := 4

vm_eval f (-100)
vm_eval f 0
vm_eval f 3
vm_eval f 5
