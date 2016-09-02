set_option new_elaborator true

attribute [eqn_sanitizer]
definition succ_eq (a : nat) : nat.succ a = a + 1 :=
rfl

attribute [eqn_sanitizer]
definition succ_add_eq (a : nat) : nat.succ (a + 1) = a + 2 :=
rfl

definition fib : nat → nat
| 0     := 1
| 1     := 1
| (n+2) := fib (n+1) + fib n

example : fib 0 = 1 := rfl
example : fib 1 = 1 := rfl
example (n : nat) : fib (n+2) = fib (n+1) + fib n := rfl

print fib._main.lemmas.eqn_3
