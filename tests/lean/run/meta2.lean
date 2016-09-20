import system.IO

meta_definition foo : nat → nat
| a := nat.cases_on a 1 (λ n, foo n + 2)

vm_eval (foo 10)

meta_definition loop : nat → IO unit
| a := do put_str ">> ", put_nat a, put_str "\n", loop (a+1)
