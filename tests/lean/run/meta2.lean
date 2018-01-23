import system.io
open io

meta definition foo : nat → nat
| a := nat.cases_on a 1 (λ n, foo n + 2)

#eval (foo 10)


meta definition loop : nat → io unit
| a := do put_str ">> ", print a, put_str "\n", loop (a+1)
