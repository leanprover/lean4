structure S :=
(x : Nat) (y : Bool) (z : Nat) (w : Nat)

set_option trace.compiler.stage1 true

def g : S → S
| s@{ x := x, ..} := { x := x + 1, ..s}
