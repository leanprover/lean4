def f (a : Unit) : Nat :=
  match a with
  | PUnit.unit => 10

#print f

def g (a : Unit) : Unit :=
  match a with
  | b@(PUnit.unit) => b

#print g
