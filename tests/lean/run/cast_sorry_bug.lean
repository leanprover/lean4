open nat

inductive Fin : ℕ → Type
| zero : Π {n : ℕ}, Fin (succ n)
| succ : Π {n : ℕ}, Fin n → Fin (succ n)

theorem foo (n m : ℕ) (a : Fin n) (b : Fin m) (H : n = m) : cast (congr_arg Fin H) a = b :=
have eq  : Fin n = Fin m, from congr_arg Fin H,
have ceq : cast eq a = b, from sorry, -- sorry implicit argument must have access to eq
sorry
