def foo (rec : nat → nat → nat) : nat → nat → nat
| 0     a := a
| (n+1) a := rec n a + a + rec n (a+1)

def main (xs : list string) : io uint32 :=
let v := fix₂ foo (xs.head.to_nat) 10 in
io.println' (to_string v) *>
pure 0
