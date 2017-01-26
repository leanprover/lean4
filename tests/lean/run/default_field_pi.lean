structure foo :=
(bar : Π n : ℕ, ℕ := id)
(baz : Π {n : ℕ}, ℕ := id)

check {foo.}
