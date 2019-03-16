def f2 (n : nat) (xs : list nat) : list (list nat) :=
let ys := list.repeat 0 n in
xs.map (λ x, x :: ys)

def main : io uint32 :=
let n := 100000 in
io.println (to_string (f2 n (list.repeat 0 n)).length) *>
pure 0
