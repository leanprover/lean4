def f : nat -> nat
| 1    := 1
| 2000 := 2
| _    := 3

#check f.equations._eqn_1
#check f.equations._eqn_2
#check f.equations._eqn_3

def g : nat -> nat
| 0    := 1
| 2000 := 2
| _    := 3

#check g.equations._eqn_1
#check g.equations._eqn_2
#check g.equations._eqn_3
