structure S :=
(x : Nat) (y : Bool) (z : Nat) (w : Nat)

setOption Trace.Compiler.stage1 True

def g : S → S
| s@{ x := x, ..} := { x := x + 1, ..s}
