
structure SCore (α : Type) :=
(x : α) (y : Nat)

inductive M
| leaf : Nat → M
| node : SCore M → M

abbrev S := SCore M

/- We use `s : S` for convenience here -/
def SCore.doubleY (s : S) : Nat :=
2 * s.y

def f (s : S) : Nat :=
s.doubleY

def g : M → Nat
| M.leaf n => n
| M.node s => s.doubleY
