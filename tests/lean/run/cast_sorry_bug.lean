import logic data.nat
open nat

inductive fin : ℕ → Type :=
| zero : Π {n : ℕ}, fin (succ n)
| succ : Π {n : ℕ}, fin n → fin (succ n)

theorem foo (n m : ℕ) (a : fin n) (b : fin m) (H : n = m) : cast (congr_arg fin H) a = b :=
have eq  : fin n = fin m, from congr_arg fin H,
have ceq : cast eq a = b, from sorry, -- sorry implicit argument must have access to eq
sorry
