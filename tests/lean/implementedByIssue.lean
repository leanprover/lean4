namespace Hidden

structure Array (α : Type u) (n : Nat) : Type u where
  data : (i : Fin n) → α

@[extern "some_extern"]
def get {α} {n : Nat}
        (A : Array α n) (i : Fin n) : α
  := A.data i

attribute [implemented_by get] Array.data -- ok

def get_2 {α : Type} {n : Nat} (A : Array α n) (i : Fin n) : α := A.data i

attribute [implemented_by get_2] Array.data -- error, number of universe parameters do not match

def get_3 {α} {n : Nat} (i : Fin n) (A : Array α n) : α := A.data i

attribute [implemented_by get_3] Array.data -- error, types do not match
