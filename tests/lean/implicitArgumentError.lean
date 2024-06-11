def foo {n : Nat} := 2*n

-- it the past, the 'n' wouldn't be in the error.
/--
error: don't know how to synthesize implicit argument 'n'
  @foo ?m.64
context:
⊢ Nat
-/
#guard_msgs in
#eval foo
