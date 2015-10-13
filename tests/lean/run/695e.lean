import data.nat
open nat
example (n : ℕ) : n + 1 = succ n :=
by rewrite [-add_one]
