@[noinline] def g (x : Nat × Nat) := x

set_option trace.compiler.boxed true
set_option trace.compiler.lambda_pure true

@[noinline] def f (b : Bool) (x : Nat × Nat) : (Nat × Nat) × (Nat × Nat) :=
let done (y : Nat × Nat) := (g (g (g x)), y) in
match b with
| true  := match x with | (a, b) := done (a, 0)
| false := match x with | (a, b) := done (0, b)

@[noinline] def h {α : Type} (x : Nat × α) := x.1

def tst2 (p : Nat × (Except Nat Nat)) : Nat × Nat :=
match p with
| (a, b) :=
  let done (x : Nat) := (h p + 1, x) in
  match b with
  | Except.ok v    := done v
  | Except.error w := done w

def main (xs : List String) : IO Unit :=
IO.println $ f true (xs.head.toNat, xs.tail.head.toNat)
