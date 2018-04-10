inductive foo : ℕ → Type
| a : foo 0
| b : ∀ n, foo (n+1)

example (n) (f : ℕ → ℕ) (h : foo (f n)) : true :=
by cases h