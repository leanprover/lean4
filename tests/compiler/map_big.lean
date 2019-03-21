def f2 (n : Nat) (xs : List Nat) : List (List Nat) :=
let ys := List.repeat 0 n in
xs.map (λ x, x :: ys)

def main : IO UInt32 :=
let n := 100000 in
IO.println (toString (f2 n (List.repeat 0 n)).length) *>
pure 0
