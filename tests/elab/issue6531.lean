-- This used to cause
-- error: The termination argument's type must not depend on the function's varying parameters

def foo (as : Array Nat) (i := 0) (j := as.size - 1) : Array Nat :=
  if j ≤ i then as
  else
    let newas := as.set! 0 0
    foo newas (i+1) (j-1)
termination_by j - i
