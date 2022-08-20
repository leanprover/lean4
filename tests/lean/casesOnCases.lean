import Lean

@[inline] def pred? (x : Nat) : Option Nat :=
  match x with
  | 0 => none
  | x+1 => some x

def isZero (x : Nat) :=
 match pred? x with
 | some _ => false
 | none => true

#eval Lean.Compiler.compile #[``isZero]

set_option trace.Compiler.simp true
#eval Lean.Compiler.compile #[``isZero]
