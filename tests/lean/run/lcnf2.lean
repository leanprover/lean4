import Lean

open Lean
set_option trace.Meta.debug true
set_option pp.proofs true

def f (x : Nat) : Nat :=
  let y := match x with
   | 0 => 1
   | x + 1 => 2 * x
  match y with
  | 0 => 2
  | z+1 => z + y + 2

#eval Compiler.compile #[``f]
