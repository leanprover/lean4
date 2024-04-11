import Lean

def issue : Trans (. < . : Nat → Nat → Prop) (. < . : Nat → Nat → Prop) (. < . : Nat → Nat → Prop) where
   trans := Nat.lt_trans

set_option trace.compiler.result true
#eval Lean.Compiler.compile #[``issue]
