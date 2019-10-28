def inc (r : IO.Ref Nat) : IO Unit :=
do v ← r.get;
   r.set (v+1);
   IO.println (">> " ++ toString v)

def initArray (r : IO.Ref (Array Nat)) (n : Nat) : IO Unit :=
n.forM $ fun i => do
  r.modify $ fun a => a.push (2*i)

def showArrayRef (r : IO.Ref (Array Nat)) : IO Unit :=
do a ← r.swap ∅;
   a.size.forM (fun i => IO.println ("[" ++ toString i ++ "]: " ++ toString (a.get! i)));
   r.swap a;
   pure ()

def tst (n : Nat) : IO Unit :=
do r₁ ← IO.mkRef 0;
   n.forM $ λ _ => inc r₁;
   r₂ ← IO.mkRef (∅ : Array Nat);
   initArray r₂ n;
   showArrayRef r₂

#eval tst 10
