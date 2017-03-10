--
open nat

variables {a : nat}

definition b : num := 2

#check (λ x, x) a + of_num b = 10
set_option pp.all true
#check (λ x, x) a + of_num b = 10
