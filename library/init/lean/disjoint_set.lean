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

namespace lean
universes u
structure disjointSet.node (α : Type u) :=
(find : α)
(rank : nat := 0)

structure disjointSet (α : Type u) [decidableEq α] [hashable α] : Type u :=
(map : hashmap α (disjointSet.node α))

def mkDisjointSet (α : Type u) [decidableEq α] [hashable α] : disjointSet α :=
⟨mkHashmap⟩

variables {α : Type u}

namespace disjointSet
variables [decidableEq α] [hashable α]

private def findAux : nat → α → hashmap α (node α) → node α
| 0     a m := { find := a, rank := 0 }
| (n+1) a m :=
  match m.find a with
  | some r := if r.find = a then r else findAux n r.find m
  | none   := { find := a, rank := 0 }

def find : disjointSet α → α → α
| ⟨m⟩ a := (findAux m.size a m).find

def rank : disjointSet α → α → nat
| ⟨m⟩ a := (findAux m.size a m).rank

def merge : disjointSet α → α → α → disjointSet α
| ⟨m⟩ a b :=
  let ra := findAux m.size a m in
  let rb := findAux m.size b m in
  if ra.find = rb.find then ⟨m⟩
  else if ra.rank < rb.rank then ⟨m.insert a { find := b }⟩
  else if ra.rank = rb.rank then ⟨(m.insert a { find := b }).insert b { find := b, rank := rb.rank + 1 }⟩
  else ⟨m.insert b { find := a }⟩

end disjointSet
end lean
