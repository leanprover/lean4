
attribute [reducible]
definition N := nat

definition f : N → nat
| 0     := 1
| (n+1) := n

example : f 0 = 1 :=
rfl
