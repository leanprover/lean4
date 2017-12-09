structure foo :=
(a b : ℕ := 2)

structure bar extends foo :=
(c : ℕ)

example (b : bar) : b.to_foo = {c := 2, ..b}.to_foo := rfl
