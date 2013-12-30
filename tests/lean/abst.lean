Import int.
Axiom PlusComm(a b : Int) : a + b == b + a.
Variable a : Int.
Check (Abst (fun x : Int, (PlusComm a x))).
SetOption pp::implicit true.
Check (Abst (fun x : Int, (PlusComm a x))).
