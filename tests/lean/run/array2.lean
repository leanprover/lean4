#check @d_array.mk

local infix ` << `:20 := array.push_back

def test1 :=
  let v1 := mk_array 3 2,
      v2 := v1 << 3 << 4,
      v3 := (v2 << 5)^.write' 0 0 in
(v1, v2, v3)

#eval test1

def tst1 (n : nat) :=
let v1 := (mk_array n 1),
    v2 := array.map (λ v, v + 1) v1 in
v2^.read' 1

#eval tst1 10
