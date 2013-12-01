Axiom PlusComm(a b : Int) : a + b == b + a.
Variable a : Int.
Check (Abst (fun x : Int, (PlusComm a x))).
Set pp::implicit true.
Check (Abst (fun x : Int, (PlusComm a x))).
