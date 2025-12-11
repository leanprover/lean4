def foo : Squash (Unit → Bool) := .mk fun _ => false

def bar : Squash Bool := foo.lift fun f => .mk !f ()

#eval! IO.println (Quot.lift id sorry bar)
