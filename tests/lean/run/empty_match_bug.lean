import data.fin
open nat
open fin

definition case0 {C : fin zero → Type} (f : fin zero) : C f :=
match f with
end
