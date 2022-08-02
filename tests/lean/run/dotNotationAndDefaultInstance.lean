namespace Ex

class Get (Cont : Type u) (Idx : Type v) (Elem : outParam (Type w)) where
  get (xs : Cont) (i : Idx) : Elem

export Get (get)

instance [Inhabited α] : Get (Array α) Nat α where
  get xs i := xs.get! i

example (as : Array (Nat × Bool)) : Bool :=
  (get as 0).2

example (as : Array (Nat × Bool)) : Bool :=
  let r1 (as : _) := (get as 0).2
  r1 as

end Ex
