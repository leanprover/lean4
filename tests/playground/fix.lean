partial def foo : Nat → Nat → Nat
| 0     a := a
| (n+1) a := foo n a + a + foo n (a+1)

def main (xs : List String) : IO UInt32 :=
let v := foo (xs.head.toNat) 10 in
IO.println (toString v) *>
pure 0
