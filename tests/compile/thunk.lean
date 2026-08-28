def compute (v : Nat) : Thunk Nat :=
⟨fun _ => let xs := List.replicate 100000 v; xs.foldl Nat.add 0⟩

@[noinline]
def test (t : Thunk Nat) (n : Nat) : Nat :=
n.repeat (fun r => t.get + r) 0

def main (xs : List String) : IO UInt32 :=
IO.println (toString (test (compute 1) 100000)) *>
pure 0
