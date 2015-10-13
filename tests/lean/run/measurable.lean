open prod nat

example (a b : nat) : size_of (a, true, bool.tt, (λ c d : nat, c + d), option.some b) = a + b :=
rfl

example : size_of (pair (pair (pair (2:nat) true) (λ a : nat, a)) (option.some (3:nat))) = 5 :=
rfl
