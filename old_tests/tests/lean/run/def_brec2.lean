set_option trace.eqn_compiler true

definition fib : nat → nat
| 0     := 1
| 1     := 1
| (n+2) := fib n + fib (n+1)

example : fib 0 = 1 := rfl
example : fib 1 = 1 := rfl
example (n : nat) : fib (n+2) = fib n + fib (n+1) := rfl
