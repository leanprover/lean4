import Int.
axiom PlusComm(a b : Int) : a + b == b + a.
variable a : Int.
check (abst (fun x : Int, (PlusComm a x))).
setoption pp::implicit true.
check (abst (fun x : Int, (PlusComm a x))).
