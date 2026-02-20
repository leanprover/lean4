

def foo : Nat -> Nat -> Nat -> List Nat
| _, _, 0   => [1]
| 0, _, _   => [2]
| n, d, k+1 => foo n d k
