new_frontend

def f (x : Nat) : Nat :=
id (_ x)

def g {α β : Type} (a : α) : α :=
a

def f3 (x : Nat) : Nat :=
let y := g x + g x;
y + _ + ?hole
