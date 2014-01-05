import Int.
axiom PlusComm(a b : Int) : a + b == b + a.
variable a : Int.
check (Abst (fun x : Int, (PlusComm a x))).
setoption pp::implicit true.
check (Abst (fun x : Int, (PlusComm a x))).
