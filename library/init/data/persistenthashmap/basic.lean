/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.array
import init.data.hashable
universes u v w w'

namespace PersistentHashMap

inductive Entry (α : Type u) (β : Type v) (σ : Type w)
| entry {} (key : α) (val : β) : Entry
| ref   {} (node : σ) : Entry
| null  {} : Entry

instance Entry.inhabited {α β σ} : Inhabited (Entry α β σ) := ⟨Entry.null⟩

inductive Node (α : Type u) (β : Type v) : Type (max u v)
| entries   (es : Array (Entry α β Node)) : Node
| collision (ks : Array α) (vs : Array β) (h : ks.size = vs.size) : Node

instance Node.inhabited {α β} : Inhabited (Node α β) := ⟨Node.entries Array.empty⟩

abbrev shift         : USize  := 5
abbrev branching     : USize  := USize.ofNat (2 ^ shift.toNat)
abbrev maxDepth      : USize  := 7
abbrev maxCollisions : Nat    := 4

def mkEmptyEntriesArray {α β} : Array (Entry α β (Node α β)) :=
(Array.mkArray PersistentHashMap.branching.toNat PersistentHashMap.Entry.null)

end PersistentHashMap

structure PersistentHashMap (α : Type u) (β : Type v) :=
(root    : PersistentHashMap.Node α β := PersistentHashMap.Node.entries PersistentHashMap.mkEmptyEntriesArray)
(size    : Nat                        := 0)

abbrev PHashMap (α : Type u) (β : Type v) := PersistentHashMap α β

namespace PersistentHashMap
variables {α : Type u} {β : Type v}

def empty : PersistentHashMap α β := {}

instance : Inhabited (PersistentHashMap α β) := ⟨{}⟩

def mkEmptyEntries {α β} : Node α β :=
Node.entries mkEmptyEntriesArray

abbrev mul2Shift (i : USize) (shift : USize) : USize := USize.shift_left i shift
abbrev div2Shift (i : USize) (shift : USize) : USize := USize.shift_right i shift
abbrev mod2Shift (i : USize) (shift : USize) : USize := USize.land i ((USize.shift_left 1 shift) - 1)

inductive IsCollisionNode : Node α β → Prop
| mk (keys : Array α) (vals : Array β) (h : keys.size = vals.size) : IsCollisionNode (Node.collision keys vals h)

abbrev CollisionNode (α β) := { n : Node α β // IsCollisionNode n }

inductive IsEntriesNode : Node α β → Prop
| mk (entries : Array (Entry α β (Node α β))) : IsEntriesNode (Node.entries entries)

abbrev EntriesNode (α β) := { n : Node α β // IsEntriesNode n }

private theorem fsetSizeEq {ks : Array α} {vs : Array β} (h : ks.size = vs.size) (i : Fin ks.size) (j : Fin vs.size) (k : α) (v : β)
                           : (ks.fset i k).size = (vs.fset j v).size :=
have h₁ : (ks.fset i k).size = ks.size from Array.szFSetEq _ _ _;
have h₂ : (vs.fset j v).size = vs.size from Array.szFSetEq _ _ _;
(h₁.trans h).trans h₂.symm

private theorem pushSizeEq {ks : Array α} {vs : Array β} (h : ks.size = vs.size) (k : α) (v : β) : (ks.push k).size = (vs.push v).size :=
have h₁ : (ks.push k).size = ks.size + 1 from Array.szPushEq _ _;
have h₂ : (vs.push v).size = vs.size + 1 from Array.szPushEq _ _;
have h₃ : ks.size + 1 = vs.size + 1      from h ▸ rfl;
(h₁.trans h₃).trans h₂.symm

partial def insertAtCollisionNodeAux [HasBeq α] : CollisionNode α β → Nat → α → β → CollisionNode α β
| n@⟨Node.collision keys vals heq, _⟩ i k v :=
  if h : i < keys.size then
    let idx : Fin keys.size := ⟨i, h⟩;
    let k' := keys.fget idx;
    if k == k' then
       let j : Fin vals.size := ⟨i, heq ▸ h⟩;
       ⟨Node.collision (keys.fset idx k) (vals.fset j v) (fsetSizeEq heq idx j k v), IsCollisionNode.mk _ _ _⟩
    else insertAtCollisionNodeAux n (i+1) k v
  else
    ⟨Node.collision (keys.push k) (vals.push v) (pushSizeEq heq k v), IsCollisionNode.mk _ _ _⟩
| ⟨Node.entries _, h⟩ _ _ _ := False.elim (nomatch h)

def insertAtCollisionNode [HasBeq α] : CollisionNode α β → α → β → CollisionNode α β :=
fun n k v => insertAtCollisionNodeAux n 0 k v

def getCollisionNodeSize : CollisionNode α β → Nat
| ⟨Node.collision keys _ _, _⟩ := keys.size
| ⟨Node.entries _, h⟩          := False.elim (nomatch h)

def mkCollisionNode (k₁ : α) (v₁ : β) (k₂ : α) (v₂ : β) : Node α β :=
let ks : Array α := Array.mkEmpty maxCollisions;
let ks := (ks.push k₁).push k₂;
let vs : Array β := Array.mkEmpty maxCollisions;
let vs := (vs.push v₁).push v₂;
Node.collision ks vs rfl

partial def insertAux [HasBeq α] [Hashable α] : Node α β → USize → USize → α → β → Node α β
| (Node.collision keys vals heq) _ depth k v :=
  let newNode := insertAtCollisionNode ⟨Node.collision keys vals heq, IsCollisionNode.mk _ _ _⟩ k v;
  if depth >= maxDepth || getCollisionNodeSize newNode < maxCollisions then newNode.val
  else match newNode with
    | ⟨Node.entries _, h⟩ => False.elim (nomatch h)
    | ⟨Node.collision keys vals heq, _⟩ =>
      let entries : Node α β := mkEmptyEntries;
      keys.iterate entries $ fun i k entries =>
        let v := vals.fget ⟨i.val, heq ▸ i.isLt⟩;
        let h := hash k;
        -- dbgTrace ("toCollision " ++ toString i ++ ", h: " ++ toString h ++ ", depth: " ++ toString depth ++ ", h': " ++
        --          toString (div2Shift h (shift * (depth - 1)))) $ fun _ =>
        let h := div2Shift h (shift * (depth - 1));
        insertAux entries h depth k v
| (Node.entries entries) h depth k v :=
  let j     := (mod2Shift h shift).toNat;
  Node.entries $ entries.modify j $ fun entry =>
    match entry with
    | Entry.null        => Entry.entry k v
    | Entry.ref node    => Entry.ref $ insertAux node (div2Shift h shift) (depth+1) k v
    | Entry.entry k' v' =>
      if k == k' then Entry.entry k v
      else Entry.ref $ mkCollisionNode k' v' k v

def insert [HasBeq α] [Hashable α] : PersistentHashMap α β → α → β → PersistentHashMap α β
| { root := n, size := sz } k v := { root := insertAux n (hash k) 1 k v, size := sz + 1 }

partial def findAtAux [HasBeq α] (keys : Array α) (vals : Array β) (heq : keys.size = vals.size) : Nat → α → Option β
| i k :=
  if h : i < keys.size then
    let k' := keys.fget ⟨i, h⟩;
    if k == k' then some (vals.fget ⟨i, heq ▸ h⟩)
    else findAtAux (i+1) k
  else none

partial def findAux [HasBeq α] : Node α β → USize → α → Option β
| (Node.entries entries) h k :=
  let j     := (mod2Shift h shift).toNat;
  match entries.get j with
  | Entry.null       => none
  | Entry.ref node   => findAux node (div2Shift h shift) k
  | Entry.entry k' v => if k == k' then some v else none
| (Node.collision keys vals heq) _ k := findAtAux keys vals heq 0 k

def find [HasBeq α] [Hashable α] : PersistentHashMap α β → α → Option β
| { root := n, .. } k := findAux n (hash k) k

partial def isUnaryEntries (a : Array (Entry α β (Node α β))) : Nat → Option (α × β) → Option (α × β)
| i acc :=
  if h : i < a.size then
    match a.fget ⟨i, h⟩ with
    | Entry.null      => isUnaryEntries (i+1) acc
    | Entry.ref _     => none
    | Entry.entry k v =>
      match acc with
      | none   => isUnaryEntries (i+1) (some (k, v))
      | some _ => none
  else acc

def isUnaryNode : Node α β → Option (α × β)
| (Node.entries entries)         := isUnaryEntries entries 0 none
| (Node.collision keys vals heq) :=
  if h : 0 < keys.size then
    some (keys.fget ⟨0, h⟩, vals.fget ⟨0, heq ▸ h⟩)
  else
    none

partial def eraseAux [HasBeq α] : Node α β → USize → α → Node α β × Bool
| n@(Node.collision keys vals heq) _ k :=
  match keys.indexOf k with
  | some idx =>
    let ⟨keys', keq⟩ := keys.eraseIdxSz idx.val;
    let ⟨vals', veq⟩ := vals.eraseIdxSz idx.val;
    have keys.size - 1 = vals.size - 1 from heq ▸ rfl;
    (Node.collision keys' vals' (keq.trans (this.trans veq.symm)), true)
  | none     => (n, false)
| n@(Node.entries entries) h k :=
  let j       := (mod2Shift h shift).toNat;
  let entry   := entries.get j;
  match entry with
  | Entry.null       => (n, false)
  | Entry.entry k' v =>
    if k == k' then (Node.entries (entries.set j Entry.null), true) else (n, false)
  | Entry.ref node   =>
    let entries := entries.set j Entry.null;
    let (newNode, deleted) := eraseAux node (div2Shift h shift) k;
    if !deleted then (n, false)
    else match isUnaryNode newNode with
      | none        => (Node.entries (entries.set j (Entry.ref newNode)), true)
      | some (k, v) => (Node.entries (entries.set j (Entry.entry k v)), true)

def erase [HasBeq α] [Hashable α] : PersistentHashMap α β → α → PersistentHashMap α β
| { root := n, size := sz } k :=
  let h := hash k;
  let (n, del) := eraseAux n h k;
  { root := n, size := if del then sz - 1 else sz }

section
variables {m : Type w → Type w'} [Monad m]
variables {σ : Type w}

@[specialize] partial def mfoldlAux (f : σ → α → β → m σ) : Node α β → σ → m σ
| (Node.collision keys vals heq) acc := keys.miterate acc $ fun i k acc => f acc k (vals.fget ⟨i.val, heq ▸ i.isLt⟩)
| (Node.entries entries) acc := entries.mfoldl (fun acc entry =>
  match entry with
  | Entry.null      => pure acc
  | Entry.entry k v => f acc k v
  | Entry.ref node  => mfoldlAux node acc)
  acc

@[specialize] def mfoldl (map : PersistentHashMap α β) (f : σ → α → β → m σ) (acc : σ) : m σ :=
mfoldlAux f map.root acc

@[specialize] def foldl (map : PersistentHashMap α β) (f : σ → α → β → σ) (acc : σ) : σ :=
Id.run $ map.mfoldl f acc
end

def toList (m : PersistentHashMap α β) : List (α × β) :=
m.foldl (fun ps k v => (k, v) :: ps) []

structure Stats :=
(numNodes      : Nat := 0)
(numNull       : Nat := 0)
(numCollisions : Nat := 0)
(maxDepth      : Nat := 0)

partial def collectStats : Node α β → Stats → Nat → Stats
| (Node.collision keys _ _) stats depth :=
  { numNodes      := stats.numNodes + 1,
    numCollisions := stats.numCollisions + keys.size - 1,
    maxDepth      := Nat.max stats.maxDepth depth,
    .. stats }
| (Node.entries entries) stats depth :=
  let stats :=
    { numNodes      := stats.numNodes + 1,
      maxDepth      := Nat.max stats.maxDepth depth,
      .. stats };
  entries.foldl (fun stats entry =>
    match entry with
    | Entry.null      => { numNull := stats.numNull + 1, .. stats }
    | Entry.ref node  => collectStats node stats (depth + 1)
    | Entry.entry _ _ => stats)
    stats

def stats (m : PersistentHashMap α β) : Stats :=
collectStats m.root {} 1

def Stats.toString (s : Stats) : String :=
"{ nodes := " ++  toString  s.numNodes ++ ", null := " ++ toString s.numNull ++
", collisions := " ++ toString s.numCollisions ++ ", depth := " ++ toString s.maxDepth ++ "}"

instance : HasToString Stats := ⟨Stats.toString⟩

end PersistentHashMap
