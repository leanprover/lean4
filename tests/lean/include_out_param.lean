class c (α : Type) (β : outParam Type) :=
(n : α → Nat)

variables {α β : Type} [c α β]

def f : Nat := 1
#print f -- don't include anything
def g (a : α) : Nat := c.n a
#print g -- include everything
