/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Array.BasicAux
import Init.Data.ToString.Macro
import Init.Data.UInt.Basic

namespace Lean
universe u v w w'

namespace PersistentHashMap

inductive Entry (α : Type u) (β : Type v) (σ : Type w) where
  | entry (key : α) (val : β) : Entry α β σ
  | ref   (node : σ) : Entry α β σ
  | null  : Entry α β σ

instance {α β σ} : Inhabited (Entry α β σ) := ⟨Entry.null⟩

inductive Node (α : Type u) (β : Type v) : Type (max u v) where
  | entries   (es : Array (Entry α β (Node α β))) : Node α β
  | collision (ks : Array α) (vs : Array β) (h : ks.size = vs.size) : Node α β

partial def Node.isEmpty : Node α β → Bool
  | .collision .. => false
  | .entries es => es.all fun
    | .entry .. => false
    | .ref n    => n.isEmpty
    | .null     => true

instance {α β} : Inhabited (Node α β) := ⟨Node.entries #[]⟩

abbrev shift         : USize  := 5
abbrev branching     : USize  := USize.ofNat (2 ^ shift.toNat)
abbrev maxDepth      : USize  := 7
abbrev maxCollisions : Nat    := 4

def mkEmptyEntriesArray {α β} : Array (Entry α β (Node α β)) :=
  (Array.mkArray PersistentHashMap.branching.toNat PersistentHashMap.Entry.null)

end PersistentHashMap

structure PersistentHashMap (α : Type u) (β : Type v) [BEq α] [Hashable α] where
  root : PersistentHashMap.Node α β := PersistentHashMap.Node.entries PersistentHashMap.mkEmptyEntriesArray

abbrev PHashMap (α : Type u) (β : Type v) [BEq α] [Hashable α] := PersistentHashMap α β

namespace PersistentHashMap

def empty [BEq α] [Hashable α] : PersistentHashMap α β := {}

def isEmpty {_ : BEq α} {_ : Hashable α} : PersistentHashMap α β → Bool
  | { root } => root.isEmpty

instance [BEq α] [Hashable α] : Inhabited (PersistentHashMap α β) := ⟨{}⟩

def mkEmptyEntries {α β} : Node α β :=
  Node.entries mkEmptyEntriesArray

abbrev mul2Shift (i : USize) (shift : USize) : USize := i.shiftLeft shift
abbrev div2Shift (i : USize) (shift : USize) : USize := i.shiftRight shift
abbrev mod2Shift (i : USize) (shift : USize) : USize := USize.land i ((USize.shiftLeft 1 shift) - 1)

inductive IsCollisionNode : Node α β → Prop where
  | mk (keys : Array α) (vals : Array β) (h : keys.size = vals.size) : IsCollisionNode (Node.collision keys vals h)

abbrev CollisionNode (α β) := { n : Node α β // IsCollisionNode n }

inductive IsEntriesNode : Node α β → Prop where
  | mk (entries : Array (Entry α β (Node α β))) : IsEntriesNode (Node.entries entries)

abbrev EntriesNode (α β) := { n : Node α β // IsEntriesNode n }

private theorem size_set {ks : Array α} {vs : Array β} (h : ks.size = vs.size) (i : Fin ks.size) (j : Fin vs.size) (k : α) (v : β)
                           : (ks.set i k).size = (vs.set j v).size := by
  simp [h]

private theorem size_push {ks : Array α} {vs : Array β} (h : ks.size = vs.size) (k : α) (v : β) : (ks.push k).size = (vs.push v).size := by
  simp [h]

partial def insertAtCollisionNodeAux [BEq α] : CollisionNode α β → Nat → α → β → CollisionNode α β
  | n@⟨Node.collision keys vals heq, _⟩, i, k, v =>
    if h : i < keys.size then
      let k' := keys[i];
      if k == k' then
         let j : Fin vals.size := ⟨i, by rw [←heq]; assumption⟩
         ⟨Node.collision (keys.set i k) (vals.set j v) (size_set heq ⟨i, h⟩ j k v), IsCollisionNode.mk _ _ _⟩
      else insertAtCollisionNodeAux n (i+1) k v
    else
      ⟨Node.collision (keys.push k) (vals.push v) (size_push heq k v), IsCollisionNode.mk _ _ _⟩
  | ⟨Node.entries _, h⟩, _, _, _ => nomatch h

def insertAtCollisionNode [BEq α] : CollisionNode α β → α → β → CollisionNode α β :=
  fun n k v => insertAtCollisionNodeAux n 0 k v

def getCollisionNodeSize : CollisionNode α β → Nat
  | ⟨Node.collision keys _ _, _⟩ => keys.size
  | ⟨Node.entries _, h⟩          => nomatch h

def mkCollisionNode (k₁ : α) (v₁ : β) (k₂ : α) (v₂ : β) : Node α β :=
  let ks : Array α := Array.mkEmpty maxCollisions
  let ks := (ks.push k₁).push k₂
  let vs : Array β := Array.mkEmpty maxCollisions
  let vs := (vs.push v₁).push v₂
  Node.collision ks vs rfl

partial def insertAux [BEq α] [Hashable α] : Node α β → USize → USize → α → β → Node α β
  | Node.collision keys vals heq, _, depth, k, v =>
    let newNode := insertAtCollisionNode ⟨Node.collision keys vals heq, IsCollisionNode.mk _ _ _⟩ k v
    if depth >= maxDepth || getCollisionNodeSize newNode < maxCollisions then newNode.val
    else match newNode with
      | ⟨Node.entries _, h⟩ => nomatch h
      | ⟨Node.collision keys vals heq, _⟩ =>
        let rec traverse (i : Nat) (entries : Node α β) : Node α β :=
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
  | Node.entries entries, h, depth, k, v =>
    let j     := (mod2Shift h shift).toNat
    Node.entries $ entries.modify j fun entry =>
      match entry with
      | Entry.null        => Entry.entry k v
      | Entry.ref node    => Entry.ref $ insertAux node (div2Shift h shift) (depth+1) k v
      | Entry.entry k' v' =>
        if k == k' then Entry.entry k v
        else Entry.ref $ mkCollisionNode k' v' k v

def insert {_ : BEq α} {_ : Hashable α} : PersistentHashMap α β → α → β → PersistentHashMap α β
  | { root }, k, v => { root := insertAux root (hash k |>.toUSize) 1 k v }

partial def findAtAux [BEq α] (keys : Array α) (vals : Array β) (heq : keys.size = vals.size) (i : Nat) (k : α) : Option β :=
  if h : i < keys.size then
    let k' := keys[i]
    have : i < vals.size := by rw [←heq]; assumption
    if k == k' then some vals[i]
    else findAtAux keys vals heq (i+1) k
  else none

partial def findAux [BEq α] : Node α β → USize → α → Option β
  | Node.entries entries, h, k =>
    let j     := (mod2Shift h shift).toNat
    match entries.get! j with
    | Entry.null       => none
    | Entry.ref node   => findAux node (div2Shift h shift) k
    | Entry.entry k' v => if k == k' then some v else none
  | Node.collision keys vals heq, _, k => findAtAux keys vals heq 0 k

def find? {_ : BEq α} {_ : Hashable α} : PersistentHashMap α β → α → Option β
  | { root }, k => findAux root (hash k |>.toUSize) k

instance {_ : BEq α} {_ : Hashable α} : GetElem (PersistentHashMap α β) α (Option β) fun _ _ => True where
  getElem m i _ := m.find? i

@[inline] def findD {_ : BEq α} {_ : Hashable α} (m : PersistentHashMap α β) (a : α) (b₀ : β) : β :=
  (m.find? a).getD b₀

@[inline] def find! {_ : BEq α} {_ : Hashable α} [Inhabited β] (m : PersistentHashMap α β) (a : α) : β :=
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

partial def findEntryAux [BEq α] : Node α β → USize → α → Option (α × β)
  | Node.entries entries, h, k =>
    let j     := (mod2Shift h shift).toNat
    match entries.get! j with
    | Entry.null       => none
    | Entry.ref node   => findEntryAux node (div2Shift h shift) k
    | Entry.entry k' v => if k == k' then some (k', v) else none
  | Node.collision keys vals heq, _, k => findEntryAtAux keys vals heq 0 k

def findEntry? {_ : BEq α} {_ : Hashable α} : PersistentHashMap α β → α → Option (α × β)
  | { root }, k => findEntryAux root (hash k |>.toUSize) k

partial def containsAtAux [BEq α] (keys : Array α) (vals : Array β) (heq : keys.size = vals.size) (i : Nat) (k : α) : Bool :=
  if h : i < keys.size then
    let k' := keys[i]
    if k == k' then true
    else containsAtAux keys vals heq (i+1) k
  else false

partial def containsAux [BEq α] : Node α β → USize → α → Bool
  | Node.entries entries, h, k =>
    let j     := (mod2Shift h shift).toNat
    match entries.get! j with
    | Entry.null       => false
    | Entry.ref node   => containsAux node (div2Shift h shift) k
    | Entry.entry k' _ => k == k'
  | Node.collision keys vals heq, _, k => containsAtAux keys vals heq 0 k

def contains [BEq α] [Hashable α] : PersistentHashMap α β → α → Bool
  | { root }, k => containsAux root (hash k |>.toUSize) k

partial def isUnaryEntries (a : Array (Entry α β (Node α β))) (i : Nat) (acc : Option (α × β)) : Option (α × β) :=
  if h : i < a.size then
    match a[i] with
    | Entry.null      => isUnaryEntries a (i+1) acc
    | Entry.ref _     => none
    | Entry.entry k v =>
      match acc with
      | none   => isUnaryEntries a (i+1) (some (k, v))
      | some _ => none
  else acc

def isUnaryNode : Node α β → Option (α × β)
  | Node.entries entries         => isUnaryEntries entries 0 none
  | Node.collision keys vals heq =>
    if h : 1 = keys.size then
      have : 0 < keys.size := by rw [←h]; decide
      have : 0 < vals.size := by rw [←heq]; assumption
      some (keys[0], vals[0])
    else
      none

partial def eraseAux [BEq α] : Node α β → USize → α → Node α β
  | n@(Node.collision keys vals heq), _, k =>
    match keys.indexOf? k with
    | some idx =>
      let keys' := keys.feraseIdx idx
      have keq := keys.size_feraseIdx idx
      let vals' := vals.feraseIdx (Eq.ndrec idx heq)
      have veq := vals.size_feraseIdx (Eq.ndrec idx heq)
      have : keys.size - 1 = vals.size - 1 := by rw [heq]
      Node.collision keys' vals' (keq.trans (this.trans veq.symm))
    | none     => n
  | n@(Node.entries entries), h, k =>
    let j       := (mod2Shift h shift).toNat
    let entry   := entries.get! j
    match entry with
    | Entry.null       => n
    | Entry.entry k' _ =>
      if k == k' then Node.entries (entries.set! j Entry.null) else n
    | Entry.ref node   =>
      let entries := entries.set! j Entry.null
      let newNode := eraseAux node (div2Shift h shift) k
      match isUnaryNode newNode with
      | none        => Node.entries (entries.set! j (Entry.ref newNode))
      | some (k, v) => Node.entries (entries.set! j (Entry.entry k v))

def erase {_ : BEq α} {_ : Hashable α} : PersistentHashMap α β → α → PersistentHashMap α β
  | { root }, k =>
    let h := hash k |>.toUSize
    { root := eraseAux root h k }

section
variable {m : Type w → Type w'} [Monad m]
variable {σ : Type w}

partial def foldlMAux (f : σ → α → β → m σ) : Node α β → σ → m σ
  | Node.collision keys vals heq, acc =>
    let rec traverse (i : Nat) (acc : σ) : m σ := do
      if h : i < keys.size then
        let k := keys[i]
        have : i < vals.size := heq ▸ h
        let v := vals[i]
        traverse (i+1) (← f acc k v)
      else
        pure acc
    traverse 0 acc
  | Node.entries entries, acc => entries.foldlM (fun acc entry =>
    match entry with
    | Entry.null      => pure acc
    | Entry.entry k v => f acc k v
    | Entry.ref node  => foldlMAux f node acc)
    acc

def foldlM {_ : BEq α} {_ : Hashable α} (map : PersistentHashMap α β) (f : σ → α → β → m σ) (init : σ) : m σ :=
  foldlMAux f map.root init

def forM {_ : BEq α} {_ : Hashable α} (map : PersistentHashMap α β) (f : α → β → m PUnit) : m PUnit :=
  map.foldlM (fun _ => f) ⟨⟩

def foldl {_ : BEq α} {_ : Hashable α} (map : PersistentHashMap α β) (f : σ → α → β → σ) (init : σ) : σ :=
  Id.run <| map.foldlM f init

protected def forIn {_ : BEq α} {_ : Hashable α} [Monad m]
    (map : PersistentHashMap α β) (init : σ) (f : α × β → σ → m (ForInStep σ)) : m σ := do
  let intoError : ForInStep σ → Except σ σ
  | .done s => .error s
  | .yield s => .ok s
  let result ← foldlM (m := ExceptT σ m) map (init := init) fun s a b =>
    (intoError <$> f (a, b) s : m _)
  match result with
  | .ok s | .error s => pure s

instance {_ : BEq α} {_ : Hashable α} : ForIn m (PersistentHashMap α β) (α × β) where
  forIn := PersistentHashMap.forIn

end

partial def mapMAux {α : Type u} {β : Type v} {σ : Type u} {m : Type u → Type w} [Monad m] (f : β → m σ) (n : Node α β) : m (Node α σ) := do
  match n with
  | .collision keys vals heq =>
    let ⟨vals', h⟩ ← vals.mapM' f
    return .collision keys vals' (h ▸ heq)
  | .entries entries =>
    let entries' ← entries.mapM fun
      | .null      => return .null
      | .entry k v => return .entry k (← f v)
      | .ref node  => return .ref (← mapMAux f node)
    return .entries entries'

def mapM {α : Type u} {β : Type v} {σ : Type u} {m : Type u → Type w} [Monad m] {_ : BEq α} {_ : Hashable α} (pm : PersistentHashMap α β) (f : β → m σ) : m (PersistentHashMap α σ) := do
  let root ← mapMAux f pm.root
  return { root }

def map {α : Type u} {β : Type v} {σ : Type u} {_ : BEq α} {_ : Hashable α} (pm : PersistentHashMap α β) (f : β → σ) : PersistentHashMap α σ :=
  Id.run <| pm.mapM f

def toList {_ : BEq α} {_ : Hashable α} (m : PersistentHashMap α β) : List (α × β) :=
  m.foldl (init := []) fun ps k v => (k, v) :: ps

def toArray {_ : BEq α} {_ : Hashable α} (m : PersistentHashMap α β) : Array (α × β) :=
  m.foldl (init := #[]) fun ps k v => ps.push (k, v)

structure Stats where
  numNodes      : Nat := 0
  numNull       : Nat := 0
  numCollisions : Nat := 0
  maxDepth      : Nat := 0

partial def collectStats : Node α β → Stats → Nat → Stats
  | Node.collision keys _ _, stats, depth =>
    { stats with
      numNodes      := stats.numNodes + 1,
      numCollisions := stats.numCollisions + keys.size - 1,
      maxDepth      := Nat.max stats.maxDepth depth }
  | Node.entries entries, stats, depth =>
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

def stats {_ : BEq α} {_ : Hashable α} (m : PersistentHashMap α β) : Stats :=
  collectStats m.root {} 1

def Stats.toString (s : Stats) : String :=
  s!"\{ nodes := {s.numNodes}, null := {s.numNull}, collisions := {s.numCollisions}, depth := {s.maxDepth}}"

instance : ToString Stats := ⟨Stats.toString⟩
