variable vec : Nat → Type
definition vec_with_len := sig len, vec len
variable n : Nat
variable v : vec n
check pair n v
check (show vec_with_len, from pair n v)
check (let v2 : vec_with_len := pair n v
       in v2)
check (pair n v : vec_with_len)
