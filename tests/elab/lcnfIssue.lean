import Lean

def issue : Trans (. < . : Nat → Nat → Prop) (. < . : Nat → Nat → Prop) (. < . : Nat → Nat → Prop) where
   trans := Nat.lt_trans

set_option trace.Compiler.result true
run_meta Lean.Compiler.compile #[``issue]
