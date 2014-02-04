variable vec : Nat → Type
definition vec_with_len := sig len, vec len
variable n : Nat
variable v : vec n
check tuple n, v
check (have vec_with_len : tuple n, v)
check (let v2 : vec_with_len := tuple n, v
       in v2)
check (tuple vec_with_len : n, v)
