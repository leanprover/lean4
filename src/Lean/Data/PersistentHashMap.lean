/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Array.BasicAux
import Init.Data.ToString.Macro

namespace Lean
universe u v w w'

namespace PersistentHashMap

inductive Entry (α : Type u) (β : Type v) (σ : Type w) where
  | entry (key : α) (val : β) : Entry α β σ
  | ref   (node : σ) : Entry α β σ
  | null  : Entry α β σ

instance {α β σ} : Inhabited (Entry α β σ) := ⟨Entry.null⟩

end PersistentHashMap

inductive PersistentHashMap (α : Type u) (β : Type v) : Type (max u v) where
  | protected entries   (es : Array (PersistentHashMap.Entry α β (PersistentHashMap α β))) : PersistentHashMap α β
  | collision (ks : Array α) (vs : Array β) (h : ks.size = vs.size) : PersistentHashMap α β

abbrev PHashMap (α : Type u) (β : Type v) [BEq α] [Hashable α] := PersistentHashMap α β

namespace PersistentHashMap

abbrev shift         : USize  := 5
abbrev branching     : USize  := USize.ofNat (2 ^ shift.toNat)
abbrev maxDepth      : USize  := 7
abbrev maxCollisions : Nat    := 4

def mkEmptyEntriesArray {α β} : Array (Entry α β (PersistentHashMap α β)) :=
  (Array.mkArray PersistentHashMap.branching.toNat PersistentHashMap.Entry.null)

def empty : PersistentHashMap α β := .entries mkEmptyEntriesArray

instance {α β} : Inhabited (PersistentHashMap α β) := ⟨empty⟩
instance {α β} : EmptyCollection (PersistentHashMap α β) := ⟨empty⟩

def mkEmptyEntries {α β} : PersistentHashMap α β :=
  .entries mkEmptyEntriesArray

abbrev mul2Shift (i : USize) (shift : USize) : USize := i.shiftLeft shift
abbrev div2Shift (i : USize) (shift : USize) : USize := i.shiftRight shift
abbrev mod2Shift (i : USize) (shift : USize) : USize := USize.land i ((USize.shiftLeft 1 shift) - 1)

inductive IsCollisionNode : PersistentHashMap α β → Prop where
  | mk (keys : Array α) (vals : Array β) (h : keys.size = vals.size) : IsCollisionNode (.collision keys vals h)

abbrev CollisionNode (α β) := { n : PersistentHashMap α β // IsCollisionNode n }

instance : Inhabited (CollisionNode α β) := ⟨⟨.collision #[] #[] rfl, .mk _ _ _⟩⟩

inductive IsEntriesNode : PersistentHashMap α β → Prop where
  | mk (entries : Array (Entry α β (PersistentHashMap α β))) : IsEntriesNode (.entries entries)

abbrev EntriesNode (α β) := { n : PersistentHashMap α β // IsEntriesNode n }

private theorem size_set {ks : Array α} {vs : Array β} (h : ks.size = vs.size) (i : Fin ks.size) (j : Fin vs.size) (k : α) (v : β)
                           : (ks.set i k).size = (vs.set j v).size := by
  simp [h]

private theorem size_push {ks : Array α} {vs : Array β} (h : ks.size = vs.size) (k : α) (v : β) : (ks.push k).size = (vs.push v).size := by
  simp [h]

partial def insertAtCollisionNodeAux [BEq α] : CollisionNode α β → Nat → α → β → CollisionNode α β
  | n@⟨.collision keys vals heq, _⟩, i, k, v =>
    if h : i < keys.size then
      let idx : Fin keys.size := ⟨i, h⟩;
      let k' := keys.get idx;
      if k == k' then
         let j : Fin vals.size := ⟨i, by rw [←heq]; assumption⟩
         ⟨.collision (keys.set idx k) (vals.set j v) (size_set heq idx j k v), IsCollisionNode.mk _ _ _⟩
      else insertAtCollisionNodeAux n (i+1) k v
    else
      ⟨.collision (keys.push k) (vals.push v) (size_push heq k v), IsCollisionNode.mk _ _ _⟩
  | ⟨.entries _, h⟩, _, _, _ => nomatch h

/-- Inserts a key-value pair into a CollisionNode, also returning whether an existing value was replaced. -/
def insertAtCollisionNode [BEq α] : CollisionNode α β → α → β → CollisionNode α β :=
  fun n k v => insertAtCollisionNodeAux n 0 k v

def getCollisionNodeSize : CollisionNode α β → Nat
  | ⟨.collision keys _ _, _⟩ => keys.size
  | ⟨.entries _, h⟩          => nomatch h

def mkCollisionNode (k₁ : α) (v₁ : β) (k₂ : α) (v₂ : β) : PersistentHashMap α β :=
  let ks : Array α := Array.mkEmpty maxCollisions
  let ks := (ks.push k₁).push k₂
  let vs : Array β := Array.mkEmpty maxCollisions
  let vs := (vs.push v₁).push v₂
  .collision ks vs rfl

/--
Inserts a key-value pair into a node, returning the new node,
along with a `Bool` indicating whether an existing value was replaced.
-/
partial def insertAux [BEq α] [Hashable α] : PersistentHashMap α β → USize → USize → α → β → PersistentHashMap α β
  | .collision keys vals heq, _, depth, k, v =>
    let newNode := insertAtCollisionNode ⟨.collision keys vals heq, IsCollisionNode.mk _ _ _⟩ k v
    if depth >= maxDepth || getCollisionNodeSize newNode < maxCollisions then newNode.val
    else
      let ⟨.collision keys vals heq, _⟩ := newNode
      let rec traverse (i : Nat) (entries : PersistentHashMap α β) : PersistentHashMap α β :=
        if h : i < keys.size then
          let k := keys[i]
          have : i < vals.size := heq ▸ h
          let v := vals[i]
          let h := hash k |>.toUSize
          let h := div2Shift h (shift * (depth - 1))
          traverse (i+1) (insertAux entries h depth k v)
        else
          entries
      traverse 0 mkEmptyEntries
  | .entries entries, h, depth, k, v =>
    let j     := (mod2Shift h shift).toNat
    -- We can't use `entries.modify` here, as we need to return `replaced`.
    -- To ensure linearity, we use `swapAt!`.
    let (entry, entries') := entries.swapAt! j .null
    match entry with
      | Entry.null        =>
        .entries $ entries'.set! j (.entry k v)
      | Entry.ref node    =>
        let newNode := insertAux node (div2Shift h shift) (depth+1) k v
        .entries $ entries'.set! j (.ref newNode)
      | Entry.entry k' v' =>
        if k == k' then .entries $ entries'.set! j (.entry k v)
        else .entries $ entries'.set! j (.ref <| mkCollisionNode k' v' k v)

partial def findAtAux [BEq α] (keys : Array α) (vals : Array β) (heq : keys.size = vals.size) (i : Nat) (k : α) : Option β :=
  if h : i < keys.size then
    let k' := keys[i]
    have : i < vals.size := by rw [←heq]; assumption
    if k == k' then some vals[i]
    else findAtAux keys vals heq (i+1) k
  else none

partial def findAux [BEq α] : PersistentHashMap α β → USize → α → Option β
  | .entries entries, h, k =>
    let j     := (mod2Shift h shift).toNat
    match entries.get! j with
    | Entry.null       => none
    | Entry.ref node   => findAux node (div2Shift h shift) k
    | Entry.entry k' v => if k == k' then some v else none
  | .collision keys vals heq, _, k => findAtAux keys vals heq 0 k

def find?  [BEq α] [Hashable α] (n : PersistentHashMap α β) (k : α) : Option β :=
  findAux n (hash k |>.toUSize) k

instance [BEq α] [Hashable α] : GetElem (PersistentHashMap α β) α (Option β) fun _ _ => True where
  getElem m i _ := m.find? i

instance [BEq α] [Hashable α] : LawfulGetElem (PersistentHashMap α β) α (Option β) fun _ _ => True where

@[inline] def findD [BEq α] [Hashable α] (m : PersistentHashMap α β) (a : α) (b₀ : β) : β :=
  (m.find? a).getD b₀

@[inline] def find! [BEq α] [Hashable α] [Inhabited β] (m : PersistentHashMap α β) (a : α) : β :=
  match m.find? a with
  | some b => b
  | none   => panic! "key is not in the map"

partial def findEntryAtAux [BEq α] (keys : Array α) (vals : Array β) (heq : keys.size = vals.size) (i : Nat) (k : α) : Option (α × β) :=
  if h : i < keys.size then
    let k' := keys[i]
    have : i < vals.size := by rw [←heq]; assumption
    if k == k' then some (k', vals[i])
    else findEntryAtAux keys vals heq (i+1) k
  else none

partial def findEntryAux [BEq α] : PersistentHashMap α β → USize → α → Option (α × β)
  | .entries entries, h, k =>
    let j     := (mod2Shift h shift).toNat
    match entries.get! j with
    | Entry.null       => none
    | Entry.ref node   => findEntryAux node (div2Shift h shift) k
    | Entry.entry k' v => if k == k' then some (k', v) else none
  | .collision keys vals heq, _, k => findEntryAtAux keys vals heq 0 k

def findEntry? [BEq α] [Hashable α] (n : PersistentHashMap α β) (k : α) : Option (α × β) :=
  findEntryAux n (hash k |>.toUSize) k

partial def containsAtAux [BEq α] (keys : Array α) (vals : Array β) (heq : keys.size = vals.size) (i : Nat) (k : α) : Bool :=
  if h : i < keys.size then
    let k' := keys[i]
    if k == k' then true
    else containsAtAux keys vals heq (i+1) k
  else false

partial def containsAux [BEq α] : PersistentHashMap α β → USize → α → Bool
  | .entries entries, h, k =>
    let j     := (mod2Shift h shift).toNat
    match entries.get! j with
    | Entry.null       => false
    | Entry.ref node   => containsAux node (div2Shift h shift) k
    | Entry.entry k' _ => k == k'
  | .collision keys vals heq, _, k => containsAtAux keys vals heq 0 k

def contains [BEq α] [Hashable α] (n : PersistentHashMap α β) (k : α) : Bool :=
  containsAux n (hash k |>.toUSize) k

def insert [BEq α] [Hashable α] (n : PersistentHashMap α β) (k : α) (v : β) : PersistentHashMap α β :=
  insertAux n (hash k |>.toUSize) 1 k v

partial def isUnaryEntries (a : Array (Entry α β (PersistentHashMap α β))) (i : Nat) (acc : Option (α × β)) : Option (α × β) :=
  if h : i < a.size then
    match a[i] with
    | Entry.null      => isUnaryEntries a (i+1) acc
    | Entry.ref _     => none
    | Entry.entry k v =>
      match acc with
      | none   => isUnaryEntries a (i+1) (some (k, v))
      | some _ => none
  else acc

def isUnaryNode : PersistentHashMap α β → Option (α × β)
  | .entries entries         => isUnaryEntries entries 0 none
  | .collision keys vals heq =>
    if h : 1 = keys.size then
      have : 0 < keys.size := by rw [←h]; decide
      have : 0 < vals.size := by rw [←heq]; assumption
      some (keys[0], vals[0])
    else
      none

partial def eraseAux [BEq α] : PersistentHashMap α β → USize → α → PersistentHashMap α β × Bool
  | n@(.collision keys vals heq), _, k =>
    match keys.indexOf? k with
    | some idx =>
      let keys' := keys.feraseIdx idx
      have keq := keys.size_feraseIdx idx
      let vals' := vals.feraseIdx (Eq.ndrec idx heq)
      have veq := vals.size_feraseIdx (Eq.ndrec idx heq)
      have : keys.size - 1 = vals.size - 1 := by rw [heq]
      (.collision keys' vals' (keq.trans (this.trans veq.symm)), true)
    | none     => (n, false)
  | n@(.entries entries), h, k =>
    let j       := (mod2Shift h shift).toNat
    let entry   := entries.get! j
    match entry with
    | Entry.null       => (n, false)
    | Entry.entry k' _ =>
      if k == k' then (.entries (entries.set! j Entry.null), true) else (n, false)
    | Entry.ref node   =>
      let entries := entries.set! j Entry.null
      let (newNode, deleted) := eraseAux node (div2Shift h shift) k
      if !deleted then (n, false)
      else match isUnaryNode newNode with
        | none        => (.entries (entries.set! j (Entry.ref newNode)), true)
        | some (k, v) => (.entries (entries.set! j (Entry.entry k v)), true)

def erase [BEq α] [Hashable α] (n : PersistentHashMap α β) (k : α) : PersistentHashMap α β :=
  let h := hash k |>.toUSize
  let (n, _del) := eraseAux n h k
  n

partial def getSize (map : PersistentHashMap α β) : Nat :=
  match map with
  | .collision keys .. => keys.size
  | .entries entries => entries.foldl (fun acc entry =>
    match entry with
    | Entry.null     => acc
    | Entry.entry .. => acc + 1
    | Entry.ref node => acc + node.getSize)
    0

section
variable {m : Type w → Type w'} [Monad m]
variable {σ : Type w}

partial def foldlM (map : PersistentHashMap α β) (f : σ → α → β → m σ) (init : σ) : m σ :=
  match map with
  | .collision keys vals heq =>
    let rec traverse (i : Nat) (acc : σ) : m σ := do
      if h : i < keys.size then
        let k := keys[i]
        have : i < vals.size := heq ▸ h
        let v := vals[i]
        traverse (i+1) (← f acc k v)
      else
        pure acc
    traverse 0 init
  | .entries entries => entries.foldlM (fun acc entry =>
    match entry with
    | Entry.null      => pure acc
    | Entry.entry k v => f acc k v
    | Entry.ref node  => foldlM node f acc)
    init

def forM (map : PersistentHashMap α β) (f : α → β → m PUnit) : m PUnit :=
  map.foldlM (fun _ => f) ⟨⟩

def foldl (map : PersistentHashMap α β) (f : σ → α → β → σ) (init : σ) : σ :=
  Id.run <| map.foldlM f init

protected def forIn [Monad m]
    (map : PersistentHashMap α β) (init : σ) (f : α × β → σ → m (ForInStep σ)) : m σ := do
  let intoError : ForInStep σ → Except σ σ
  | .done s => .error s
  | .yield s => .ok s
  let result ← foldlM (m := ExceptT σ m) map (init := init) fun s a b =>
    (intoError <$> f (a, b) s : m _)
  match result with
  | .ok s | .error s => pure s

instance : ForIn m (PersistentHashMap α β) (α × β) where
  forIn := PersistentHashMap.forIn

end

partial def mapM {α : Type u} {β : Type v} {σ : Type u} {m : Type u → Type w} [Monad m] (pm : PersistentHashMap α β) (f : β → m σ) : m (PersistentHashMap α σ) := do
  match pm with
  | .collision keys vals heq =>
    let ⟨vals', h⟩ ← vals.mapM' f
    return .collision keys vals' (h ▸ heq)
  | .entries entries =>
    let entries' ← entries.mapM fun
      | .null      => return .null
      | .entry k v => return .entry k (← f v)
      | .ref node  => return .ref (← mapM node f)
    return .entries entries'

def map {α : Type u} {β : Type v} {σ : Type u} (pm : PersistentHashMap α β) (f : β → σ) : PersistentHashMap α σ :=
  Id.run <| pm.mapM f

def toList (m : PersistentHashMap α β) : List (α × β) :=
  m.foldl (init := []) fun ps k v => (k, v) :: ps

def toArray (m : PersistentHashMap α β) : Array (α × β) :=
  m.foldl (init := #[]) fun ps k v => ps.push (k, v)

structure Stats where
  numNodes      : Nat := 0
  numNull       : Nat := 0
  numCollisions : Nat := 0
  maxDepth      : Nat := 0

partial def collectStats : PersistentHashMap α β → Stats → Nat → Stats
  | .collision keys _ _, stats, depth =>
    { stats with
      numNodes      := stats.numNodes + 1,
      numCollisions := stats.numCollisions + keys.size - 1,
      maxDepth      := Nat.max stats.maxDepth depth }
  | .entries entries, stats, depth =>
    let stats :=
      { stats with
        numNodes      := stats.numNodes + 1,
        maxDepth      := Nat.max stats.maxDepth depth }
    entries.foldl (fun stats entry =>
      match entry with
      | Entry.null      => { stats with numNull := stats.numNull + 1 }
      | Entry.ref node  => collectStats node stats (depth + 1)
      | Entry.entry _ _ => stats)
      stats

def stats (m : PersistentHashMap α β) : Stats :=
  collectStats m {} 1

def Stats.toString (s : Stats) : String :=
  s!"\{ nodes := {s.numNodes}, null := {s.numNull}, collisions := {s.numCollisions}, depth := {s.maxDepth}}"

instance : ToString Stats := ⟨Stats.toString⟩

end PersistentHashMap

structure PersistentHashMapSized (α : Type u) (β : Type v) [BEq α] [Hashable α] where
  root    : PersistentHashMap α β := .entries PersistentHashMap.mkEmptyEntriesArray
  size    : Nat                   := 0

abbrev PHashMapSized (α : Type u) (β : Type v) [BEq α] [Hashable α] := PersistentHashMapSized α β

namespace PersistentHashMapSized

def empty [BEq α] [Hashable α] : PersistentHashMapSized α β := {}

def isEmpty [BEq α] [Hashable α] (m : PersistentHashMapSized α β) : Bool :=
  m.size == 0

instance [BEq α] [Hashable α] : Inhabited (PersistentHashMapSized α β) := ⟨{}⟩

@[inline] def find? {_ : BEq α} {_ : Hashable α} : PersistentHashMapSized α β → α → Option β
  | { root := n, .. }, k => PersistentHashMap.findAux n (hash k |>.toUSize) k

instance {_ : BEq α} {_ : Hashable α} : GetElem (PersistentHashMapSized α β) α (Option β) fun _ _ => True where
  getElem m i _ := m.find? i

instance {_ : BEq α} {_ : Hashable α} : LawfulGetElem (PersistentHashMapSized α β) α (Option β) fun _ _ => True where

@[inline] def findD {_ : BEq α} {_ : Hashable α} (m : PersistentHashMapSized α β) (a : α) (b₀ : β) : β :=
  (m.find? a).getD b₀

@[inline] def find! {_ : BEq α} {_ : Hashable α} [Inhabited β] (m : PersistentHashMapSized α β) (a : α) : β :=
  match m.find? a with
  | some b => b
  | none   => panic! "key is not in the map"

@[inline] def findEntry? {_ : BEq α} {_ : Hashable α} (m : PersistentHashMapSized α β) (k : α) : Option (α × β) :=
  m.root.findEntry? k

@[inline] def contains [BEq α] [Hashable α] (m : PersistentHashMapSized α β) (k : α) : Bool :=
  m.root.contains k

@[inline] def insertNew {_ : BEq α} {_ : Hashable α} : PersistentHashMapSized α β → α → β → PersistentHashMapSized α β
  | { root := n, size := sz }, k, v =>
    { root := n.insert k v, size := sz + 1 }

@[inline] def replace {_ : BEq α} {_ : Hashable α} : PersistentHashMapSized α β → α → β → PersistentHashMapSized α β
  | { root := n, size := sz }, k, v =>
    { root := n.insert k v, size := sz }

def insert {_ : BEq α} {_ : Hashable α} : PersistentHashMapSized α β → α → β → PersistentHashMapSized α β
  | { root := n, size := sz }, k, v =>
    let hash := hash k |>.toUSize
    let replaced := n.containsAux hash k
    let node := n.insertAux hash 1 k v
    { root := node, size := if replaced then sz else sz + 1 }

def erase {_ : BEq α} {_ : Hashable α} : PersistentHashMapSized α β → α → PersistentHashMapSized α β
  | { root := n, size := sz }, k =>
    let h := hash k |>.toUSize
    let (n, del) := n.eraseAux h k
    { root := n, size := if del then sz - 1 else sz }

section
variable {m : Type w → Type w'} [Monad m]
variable {σ : Type w}

@[inline] def foldlM {_ : BEq α} {_ : Hashable α} (map : PersistentHashMapSized α β) (f : σ → α → β → m σ) (init : σ) : m σ :=
  map.root.foldlM f init

@[inline] def forM {_ : BEq α} {_ : Hashable α} (map : PersistentHashMapSized α β) (f : α → β → m PUnit) : m PUnit :=
  map.foldlM (fun _ => f) ⟨⟩

@[inline] def foldl {_ : BEq α} {_ : Hashable α} (map : PersistentHashMapSized α β) (f : σ → α → β → σ) (init : σ) : σ :=
  Id.run <| map.foldlM f init

instance {_ : BEq α} {_ : Hashable α} : ForIn m (PersistentHashMapSized α β) (α × β) where
  forIn m := m.root.forIn

end

@[inline] def mapM {α : Type u} {β : Type v} {σ : Type u} {m : Type u → Type w} [Monad m] {_ : BEq α} {_ : Hashable α} (pm : PersistentHashMapSized α β) (f : β → m σ) : m (PersistentHashMapSized α σ) := do
  let root ← pm.root.mapM f
  return { pm with root }

@[inline] def map {α : Type u} {β : Type v} {σ : Type u} {_ : BEq α} {_ : Hashable α} (pm : PersistentHashMapSized α β) (f : β → σ) : PersistentHashMapSized α σ :=
  Id.run <| pm.mapM f

@[inline] def toList {_ : BEq α} {_ : Hashable α} (m : PersistentHashMapSized α β) : List (α × β) :=
  m.root.toList

@[inline] def toArray {_ : BEq α} {_ : Hashable α} (m : PersistentHashMapSized α β) : Array (α × β) :=
  m.root.toArray
