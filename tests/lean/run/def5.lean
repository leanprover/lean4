

def fib : Nat → Nat
| 0   => 1
| 1   => 1
| n+2 => fib n + fib (n+1)

example : fib 0 = 1 := rfl
example : fib 1 = 1 := rfl
example (n : Nat) : fib (n+2) = fib n + fib (n+1) := rfl
