import Lean

def f (x y z : Nat) : Array Nat :=
  #[x, y, z, y, x]

set_option trace.Compiler.result true
#eval Lean.Compiler.compile #[``f]
