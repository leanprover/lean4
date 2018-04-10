inductive foo : nat → Type
| f1 : foo 1
| fn : Pi (n : nat), foo n

def rig : Pi (n : nat), foo n → bool
| 1  foo.f1 := tt
| _    _    := ff
