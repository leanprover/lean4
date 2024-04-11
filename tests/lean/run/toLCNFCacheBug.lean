import Lean

def f' (x y : Nat) :=
  let s := (x, y)
  let y := s.2
  y + s.2

set_option trace.compiler true
#eval Lean.Compiler.compile #[``f']
