namespace Ex

class Get (Cont : Type u) (Idx : Type v) (Elem : outParam (Type w)) where
  get (xs : Cont) (i : Idx) : Elem

export Get (get)

instance [Inhabited α] : Get (Array α) Nat α where
  get xs i := xs.get! i

instance : Coe Bool Nat where
  coe b := if b then 1 else 0

def g (as : Array (Array Bool)) : Nat :=
  let bs := get as 0
  get bs 0

def h (as : Array (Array Bool)) (i : Nat) : Nat :=
  let bs := get as i
  get bs i

end Ex
