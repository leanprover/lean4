structure foo :=
(bar : Π n : ℕ, ℕ := id)
(baz : Π {n : ℕ}, ℕ := id)
(bat : Π n : ℕ, ℕ := λ n, n)

check {foo.}
