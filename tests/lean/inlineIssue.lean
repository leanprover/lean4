import Lean

def f (x : Nat) :=
  let g (y z : Nat) := match y with | 0 => x * z * x * y * y | .succ y  => y + z
  let h (x : Nat) := g x x
  h (x+1) +
  h (x+2) +
  h (x+3) +
  h (x+4) +
  h (x+5) +
  h (x+6) +
  h (x+7) +
  h (x+8) +
  h (x+9)

#eval Lean.Compiler.compile #[``f]

set_option trace.Compiler.simp true
#eval Lean.Compiler.compile #[``f]
