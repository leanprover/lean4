structure S :=
(x : nat) (y : bool) (z : nat) (w : nat)

set_option trace.compiler.stage1 true

def g : S → S
| s@{ x := x, ..} := { x := x + 1, ..s}
