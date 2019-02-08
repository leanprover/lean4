def compute (v : nat) : thunk nat :=
⟨λ _, let xs := list.repeat v 100000 in xs.foldl (+) 0⟩

@[noinline]
def test (t : thunk nat) (n : nat) : nat :=
n.repeat (λ i r, t.get + r) 0

def main (xs : list string) : io uint32 :=
io.println' (to_string (test (compute 1) 100000)) *>
pure 0
