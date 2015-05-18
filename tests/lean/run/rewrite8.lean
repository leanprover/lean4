import data.nat
open nat
constant f : nat → nat

theorem tst1 (x y : nat) (H1 : (λ z, z + 0) x = y) : f x = f y :=
by rewrite [▸* at H1, ^add at H1, H1]
