--

universe u

def Below (n : Nat) : Nat → Prop :=
  (· < n)

def f {n : Nat} (v : Subtype (Below n)) : Nat :=
  (coe v) + 1

instance pred2subtype {α : Type u} : CoeSort (α → Prop) (Type u) :=
  CoeSort.mk (fun p => Subtype p)

def g {n : Nat} (v : Below n) : Nat :=
  v.val + 1
