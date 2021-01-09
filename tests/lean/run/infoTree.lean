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

def h : (x : Nat) → x + 0 = x :=
  fun x => by
    simp
    exact rfl

showInfoTrees!
