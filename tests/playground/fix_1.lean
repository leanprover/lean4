def foo (rec : Nat → Nat → Nat) : Nat → Nat → Nat
| 0     a := a
| (n+1) a := rec n a + a + rec n (a+1)

def main (xs : List String) : IO UInt32 :=
let v := fix1 foo (xs.head.toNat) 10 in
IO.println (toString v) *>
pure 0
