def inc (r : IO.Ref Nat) : IO Unit :=
do v ← r.get,
   r.set (v+1),
   IO.println (">> " ++ toString v)

def initArray (r : IO.Ref (Array Nat)) (n : Nat) : IO Unit :=
n.mrepeat $ λ i, do
  r.modify $ λ a, a.push (2*i)

def showArrayRef (r : IO.Ref (Array Nat)) : IO Unit :=
do a ← r.swap ∅,
   a.size.mrepeat (λ i, IO.println ("[" ++ toString i ++ "]: " ++ toString (a.get i))),
   r.swap a,
   pure ()

def main (xs : List String) : IO Unit :=
do let n := xs.head.toNat,
   r₁ ← IO.mkRef 0,
   n.mrepeat (λ _, inc r₁),
   r₂ ← IO.mkRef (∅ : Array Nat),
   initArray r₂ n,
   showArrayRef r₂
