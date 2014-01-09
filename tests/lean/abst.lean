import Int.
axiom PlusComm(a b : Int) : a + b == b + a.
variable a : Int.
check (funext (fun x : Int, (PlusComm a x))).
set_option pp::implicit true.
check (funext (fun x : Int, (PlusComm a x))).
