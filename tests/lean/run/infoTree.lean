import Lean

open Lean.Elab

elab "enableInfo!" : command  => enableInfoTree

elab "showInfoTrees!" : command => do
  let trees ← getInfoTrees
  trees.forM fun tree => do
    logInfo f!"{← tree.format}"

structure A where
  val : Nat → Nat

structure B where
  pair : A × A

enableInfo!

def f (x : Nat) : Nat × Nat :=
  let y := ⟨x, x⟩
  id y

def h : (x y : Nat) → (b : Bool) → x + 0 = x :=
  fun x y b => by
    simp
    exact rfl

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

showInfoTrees!
