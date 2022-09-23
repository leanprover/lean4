import Lean

inductive MyEmpty

def f (x : MyEmpty) : Nat :=
  MyEmpty.casesOn x

set_option trace.Compiler.result true
#eval Lean.Compiler.compile #[``f]
