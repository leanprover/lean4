new_frontend

universes u

def Below (n : Nat) : Nat → Prop :=
(· < n)

def f {n : Nat} (v : Subtype (Below n)) : Nat :=
v.val + 1

instance pred2subtype {α : Type u} (p : α → Prop) : CoeSort (α → Prop) p (Type u) :=
CoeSort.mk _ (Subtype p)

def g {n : Nat} (v : Below n) : Nat :=
v.val + 1
