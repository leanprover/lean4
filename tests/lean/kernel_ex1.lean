variable N : Type
variable a : N
check fun x : a, x
check a a
variable f : N -> N
check f (fun x : N, x)