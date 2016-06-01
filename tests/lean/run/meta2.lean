import system.IO

meta_definition foo (a : nat) : nat :=
nat.cases_on a 1 (λ n, foo n + 2)

vm_eval (foo 10)

meta_definition loop (a : nat) : IO unit :=
do put_str ">> ", put_nat a, put_str "\n", loop (a+1)
