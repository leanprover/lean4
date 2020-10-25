

@[noinline] def g (x : Nat) : Nat × Nat := (x, x)
@[noinline] def p (x : Nat) : Bool := x > 10

set_option trace.compiler.ir.rc true

def f (x : Nat) (y : Nat) : Bool :=
let jp (x : Nat) : Bool := -- x must be owned
  p x || p (x+1)
match x with
| 0 => let z := g y; jp z.1
| _ => let z := g x; jp z.1

def h (x : Nat) : Bool := -- x must be borrowed
x > 5
