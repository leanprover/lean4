import data.nat
open nat

example (x : ℕ) : 0 = x * 0 :=
calc 0 = x * 0 : nat.mul_zero
