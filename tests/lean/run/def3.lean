
definition f (a b : nat) : nat :=
nat.cases_on a
  (a + b + a + a + b)
  (λ a', a + a + b)

definition g (a b : nat) :=
f (f a b) a

set_option trace.compiler true

#eval g (g (f 2 3) 2) 3
