import data.finset
open nat list finset

example : to_finset [1, 3, 1] = to_finset [3, 3, 3, 1] :=
dec_trivial

example : to_finset [1, 2] ∪ to_finset [1, 3] = to_finset [3, 2, 1] :=
dec_trivial

example : 1 ∈ to_finset [3, 2, 1] :=
dec_trivial

example : bigsum (to_finset [3, 2, 2]) (λ x, x*x) = 13 :=
rfl

example : bigprod (to_finset [1, 2]) (λ x, x+1) = 6 :=
rfl
