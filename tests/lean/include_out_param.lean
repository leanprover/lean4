class c (α : Type) (β : out_param Type) :=
(n : α → nat)

variables {α β : Type} [c α β]

def f : nat := 1
#print f -- don't include anything
def g (a : α) : nat := c.n a
#print g -- include everything
