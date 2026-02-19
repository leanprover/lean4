def foo : Squash (Unit → Bool) := .mk fun _ => false

def bar : Squash Bool := foo.lift fun f => .mk !f ()

set_option trace.Compiler.result true
#eval unsafeCast (β := Bool) bar
#eval! IO.println (Quot.lift id sorry bar)
