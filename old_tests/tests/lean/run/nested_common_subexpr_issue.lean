-- set_option trace.compiler true

def fib_aux : ℕ → ℕ × ℕ
| 0     := (0, 1)
| (n+1) := let p := fib_aux n in (p.2, p.1 + p.2)

def fib (n) := (fib_aux n).2

#eval fib 10000

def fib_aux2 : ℕ → ℕ × ℕ
| 0     := (0, 1)
| (n+1) := let (a, b) := fib_aux2 n in (b, a + b)

def fib2 (n) := (fib_aux2 n).2

#eval fib2 10000
