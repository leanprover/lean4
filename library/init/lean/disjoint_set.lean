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
structure disjoint_set.node (α : Type u) :=
(find : α)
(rank : nat := 0)

structure disjoint_set (α : Type u) [decidable_eq α] [hashable α] : Type u :=
(map : hashmap α (disjoint_set.node α))

variables {α : Type u}

def mk_disjoint_set [decidable_eq α] [hashable α] : disjoint_set α :=
⟨mk_hashmap⟩

namespace disjoint_set
variables [decidable_eq α] [hashable α]

private def find_aux : nat → α → hashmap α (node α) → node α
| 0     a m := { find := a, rank := 0 }
| (n+1) a m :=
  match m.find a with
  | some r := if r.find = a then r else find_aux n r.find m
  | none   := { find := a, rank := 0 }

def find : disjoint_set α → α → α
| ⟨m⟩ a := (find_aux m.size a m).find

def rank : disjoint_set α → α → nat
| ⟨m⟩ a := (find_aux m.size a m).rank

def merge : disjoint_set α → α → α → disjoint_set α
| ⟨m⟩ a b :=
  let ra := find_aux m.size a m in
  let rb := find_aux m.size b m in
  if ra.find = rb.find then ⟨m⟩
  else if ra.rank < rb.rank then ⟨m.insert a { find := b }⟩
  else if ra.rank = rb.rank then ⟨(m.insert a { find := b }).insert b { find := b, rank := rb.rank + 1 }⟩
  else ⟨m.insert b { find := a }⟩

end disjoint_set
end lean
