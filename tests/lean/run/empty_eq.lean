import data.fin
open nat
open fin

definition case0 {C : fin zero → Type} : Π (f : fin zero), C f
| [none]


print definition case0
