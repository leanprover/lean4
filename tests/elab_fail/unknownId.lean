macro "foo" : term => `(bla)

#check foo

def f (bla : Nat) : Nat :=
  foo

macro "boo" x:term : term => `(fun (bla : Nat) => $x + bla)

def g : Nat → Nat :=
  boo foo
