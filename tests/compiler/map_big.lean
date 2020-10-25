
def f2 (n : Nat) (xs : List Nat) : List (List Nat) :=
let ys := List.replicate n 0;
xs.map (fun x => x :: ys)

def main : IO UInt32 :=
let n := 100000;
IO.println (toString (f2 n (List.replicate n 0)).length) *>
pure 0
