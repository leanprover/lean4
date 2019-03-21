def inc (r : IO.ref Nat) : IO Unit :=
do v ← r.read,
   r.write (v+1),
   IO.println (">> " ++ toString v)

def initArray (r : IO.ref (Array Nat)) (n : Nat) : IO Unit :=
n.mrepeat $ λ i, do
  r.modify $ λ a, a.push (2*i)

def showArrayRef (r : IO.ref (Array Nat)) : IO Unit :=
do a ← r.swap Array.nil,
   a.size.mrepeat (λ i, IO.println ("[" ++ toString i ++ "]: " ++ toString (a.read' i))),
   r.swap a,
   pure ()

def main (xs : List String) : IO Unit :=
do let n := xs.head.toNat,
   r₁ ← IO.mkRef 0,
   n.mrepeat (λ _, inc r₁),
   r₂ ← IO.mkRef (Array.nil : Array Nat),
   initArray r₂ n,
   showArrayRef r₂
