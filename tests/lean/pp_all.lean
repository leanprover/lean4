open nat

variables {a : nat}

abbreviation b := 2

check (λ x, x) a + b = 10
set_option pp.all true
check (λ x, x) a + b = 10
