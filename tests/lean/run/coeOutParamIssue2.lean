namespace Ex
class GetElem (Cont : Type u) (Idx : Type v) (Elem : outParam (Type w)) where
  getElem (xs : Cont) (i : Idx) : Elem

export GetElem (getElem)

instance : GetElem (Array α) Nat α where
  getElem xs i := xs.get i sorry

opaque f : Option Bool → Bool
opaque g : Bool → Bool

def bad (xs : Array Bool) : Bool :=
  let x := getElem xs 0
  f x && g x
end Ex
