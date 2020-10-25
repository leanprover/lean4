

macro "m" x:term : term => `(fun x => $x)

set_option trace.Elab.step true in
#check fun x => m x
