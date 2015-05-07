variables (A : Type) [H : inhabited A] (x : A)
include H

definition foo := x
check foo  -- A and x are explicit

variables {A x}
definition foo' := x
check @foo' -- A is explicit, x is implicit

open nat

check foo nat 10

definition test : foo' = 10 := rfl

set_option pp.implicit true
print test
