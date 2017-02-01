meta def mk_value (n : nat) : nat :=
trace "mk_value" (2 * n)

meta def mk_fn (sz : nat) : nat → nat :=
let n := mk_value sz in
λ x, x + n

vm_eval let f := mk_fn 10 in f 1 + f 2 + f 3 + f 4


vm_eval ((let x := mk_value 10 in mk_fn x) 10)
