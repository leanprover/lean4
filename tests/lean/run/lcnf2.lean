import Lean

open Lean

def f (x : Nat) : Nat :=
  let y := match x with
   | 0 => 1
   | x + 1 => 2 * x
  match y with
  | 0 => 2
  | z+1 => z + y + 2

set_option trace.Compiler true

def g (x : Nat) : Bool :=
  let pred? := match x with
    | 0 => none
    | y+1 => some y
  match pred? with
  | none => true
  | some _  => false


abbrev TupleNTyp : Nat → Type 1
  | 0 => Type
  | n + 1 => Type → (TupleNTyp n)

noncomputable abbrev TupleN : (n : Fin 1) → TupleNTyp n.val
  | 0 => Unit × Unit

set_option pp.proofs true
#eval Compiler.compile #[``TupleN]


def userControlled (a b : Nat) :=
  let f := fun _ => a
  f () + b

#eval Compiler.compile #[``userControlled]
