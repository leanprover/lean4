/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.data.hashmap.basic

/- Disjoint set datastructure using union-find algorithm.
   We use hashmaps to implement. Thus, we should be disjoint sets
   linearly for optimal performace. -/

namespace Lean
universes u
structure DisjointSet.Node (α : Type u) :=
(find : α)
(rank : Nat := 0)

structure DisjointSet (α : Type u) [DecidableEq α] [Hashable α] : Type u :=
(map : Hashmap α (DisjointSet.Node α))

def mkDisjointSet (α : Type u) [DecidableEq α] [Hashable α] : DisjointSet α :=
⟨mkHashmap⟩

variables {α : Type u}

namespace DisjointSet
variables [DecidableEq α] [Hashable α]

private def findAux : Nat → α → Hashmap α (Node α) → Node α
| 0     a m := { find := a, rank := 0 }
| (n+1) a m :=
  match m.find a with
  | some r := if r.find = a then r else findAux n r.find m
  | none   := { find := a, rank := 0 }

def find : DisjointSet α → α → α
| ⟨m⟩ a := (findAux m.size a m).find

def rank : DisjointSet α → α → Nat
| ⟨m⟩ a := (findAux m.size a m).rank

def merge : DisjointSet α → α → α → DisjointSet α
| ⟨m⟩ a b :=
  let ra := findAux m.size a m in
  let rb := findAux m.size b m in
  if ra.find = rb.find then ⟨m⟩
  else if ra.rank < rb.rank then ⟨m.insert a { find := b }⟩
  else if ra.rank = rb.rank then ⟨(m.insert a { find := b }).insert b { find := b, rank := rb.rank + 1 }⟩
  else ⟨m.insert b { find := a }⟩

end DisjointSet
end Lean
