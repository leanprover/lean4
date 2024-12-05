namespace Ex
class GetElem (Cont : Type u) (Idx : Type v) (Elem : outParam (Type w)) where
  getElem (xs : Cont) (i : Idx) : Elem

export GetElem (getElem)

instance : GetElem (Array α) Nat α where
  getElem xs i := xs.get i sorry

opaque f : Option Bool → Id Unit

def bad2 (bs : Array Bool) (n : Nat) : Id Unit := do
  for idx in [:n] do
    let b  := getElem bs idx
    f b

def bad3 (bs : Array Bool) (n : Nat) : Id Unit := do
  for h : idx in [:n] do
    let b  := getElem bs idx
    f b

end Ex
