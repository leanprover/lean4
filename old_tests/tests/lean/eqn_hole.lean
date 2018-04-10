
definition f : nat → nat
| 0 := _


definition g : nat → nat
| 0     := 0
| (n+1) := g _ + 1
