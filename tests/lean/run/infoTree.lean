import Lean

open Lean.Elab

elab "enableInfo!" : command  => enableInfoTree

elab "showInfoTrees!" : command => do
  let trees ← getInfoTrees
  trees.forM fun tree => do
    IO.println f!"{← tree.format}"

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

showInfoTrees!
