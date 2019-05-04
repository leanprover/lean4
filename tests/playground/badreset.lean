@[noinline] def g (x : Nat × Nat) := x

set_option trace.compiler.boxed true

@[noinline] def f (b : Bool) (x : Nat × Nat) : (Nat × Nat) × (Nat × Nat) :=
let done (y : Nat × Nat) := (g (g (g y)), x) in
match b with
| true  := match x with | (a, b) := done (a, 0)
| false := match x with | (a, b) := done (0, b)

def main (xs : List String) : IO Unit :=
IO.println $ f true (xs.head.toNat, xs.tail.head.toNat)
