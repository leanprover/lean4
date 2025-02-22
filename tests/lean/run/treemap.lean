/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
import Std.Data.TreeSet.Basic
import Std.Data.TreeSet.Lemmas

open Std

variable {α : Type u} {β : Type v} [Ord α]

def mkDTreeMapSingleton (a : α) (b : β) : DTreeMap α (fun _ => β) := Id.run do
  let mut m : DTreeMap α (fun _ => β) := ∅
  m := m.insert a b
  return m

def mkTreeMapSingleton (a : α) (b : β) : TreeMap α β := Id.run do
  let mut m : TreeMap α β := ∅
  m := m.insert a b
  return m

def mkTreeSetSingleton (a : α) : TreeSet α := Id.run do
  let mut m : TreeSet α := ∅
  m := m.insert a
  return m

example [TransOrd α] [LawfulEqOrd α] (a : α) (b : β) : Option β :=
  mkDTreeMapSingleton a b |>.get? a

example [TransOrd α] [LawfulEqOrd α] (a : α) (b : β) : Option β :=
  (mkTreeMapSingleton a b)[a]?

example [TransOrd α] (a : α) (b : β) : (mkTreeMapSingleton a b).contains a := by
  simp [mkTreeMapSingleton, Id.run]

example [TransOrd α] (a : α) (b : β) : (mkDTreeMapSingleton a b).contains a := by
  simp [mkDTreeMapSingleton, Id.run]

example [TransOrd α] (a : α) : (mkTreeSetSingleton a).contains a := by
  simp [mkTreeSetSingleton, Id.run]
