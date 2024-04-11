import Lean

inductive MyEmpty

def f (x : MyEmpty) : Nat :=
  MyEmpty.casesOn x

set_option trace.compiler.result true
#eval Lean.Compiler.compile #[``f]
