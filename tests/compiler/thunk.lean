def compute (v : Nat) : Thunk Nat :=
⟨λ _, let xs := List.repeat v 100000 in xs.foldl (+) 0⟩

@[noinline]
def test (t : Thunk Nat) (n : Nat) : Nat :=
n.repeat (λ i r, t.get + r) 0

def main (xs : List String) : IO UInt32 :=
IO.println (toString (test (compute 1) 100000)) *>
pure 0
