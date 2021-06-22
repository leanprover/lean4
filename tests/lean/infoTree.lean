import Lean

open Lean.Elab

structure A where
  val : Nat → Nat

structure B where
  pair : A × A

set_option trace.Elab.info true

def f (x : Nat) : Nat × Nat :=
  let y := ⟨x, x⟩
  id y

def h : (x y : Nat) → (b : Bool) → x + 0 = x :=
  fun x y b => by
    simp

def f2 : (x y : Nat) → (b : Bool) → Nat :=
  fun x y b =>
    let (z, w) := (x + y, x - y)
    let z1 := z + w
    z + z1

def f3 (s : Nat × Array (Array Nat)) : Array Nat :=
  s.2[1].push s.1

def f4 (arg : B) : Nat :=
  arg.pair.fst.val 0

def f5 (x : Nat) : B := {
  pair := ({ val := id }, { val := id })
}

open Nat in
#print xor
