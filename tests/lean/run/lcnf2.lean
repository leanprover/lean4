import Lean

open Lean

def f (x : Nat) : Nat :=
  let y := match x with
   | 0 => 1
   | x + 1 => 2 * x
  match y with
  | 0 => 2
  | z+1 => z + y + 2

#eval Compiler.compile #[``f]

def g (x : Nat) : Bool :=
  let pred? := match x with
    | 0 => none
    | y+1 => some y
  match pred? with
  | none => true
  | some _  => false

set_option trace.Compiler.step true
#eval Compiler.compile #[``g]
