class C (α : Type) where
  op : α → α → α

inductive X
| mk : Nat → X

instance : C X where
  op (X.mk a) (X.mk b) := X.mk (a + b)
