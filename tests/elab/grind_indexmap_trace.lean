import Std.Data.HashMap

macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| grind)

open Std

structure IndexMap (α : Type u) (β : Type v) [BEq α] [Hashable α] where
  private indices : HashMap α Nat
  private keys : Array α
  private values : Array β
  private size_keys' : keys.size = values.size := by grind
  private WF1 : ∀ (i : Nat) (h1 : i < keys.size) (h2 : keys[i] ∈ indices), indices[keys[i]] = i := by grind
  private WF2 : ∀ (a : α) (h1 : a ∈ indices) (h2 : indices[a] < keys.size), keys[indices[a]] = a := by grind
  private WF3 : ∀ (a : α) (h1 : a ∈ indices), indices[a] < keys.size := by grind
  private WF4 : ∀ (i : Nat) (h1 : i < keys.size), keys[i] ∈ indices := by grind

namespace IndexMap

variable {α : Type u} {β : Type v} [BEq α] [Hashable α]
variable {m : IndexMap α β} {a : α} {b : β} {i : Nat}

@[inline] def size (m : IndexMap α β) : Nat :=
  m.values.size

@[local grind =] private theorem size_keys : m.keys.size = m.size := m.size_keys'

def emptyWithCapacity (capacity := 8) : IndexMap α β where
  indices := HashMap.emptyWithCapacity capacity
  keys := Array.emptyWithCapacity capacity
  values := Array.emptyWithCapacity capacity

instance : EmptyCollection (IndexMap α β) where
  emptyCollection := emptyWithCapacity

instance : Inhabited (IndexMap α β) where
  default := ∅

@[inline] def contains (m : IndexMap α β)
    (a : α) : Bool :=
  m.indices.contains a

instance : Membership α (IndexMap α β) where
  mem m a := a ∈ m.indices

instance {m : IndexMap α β} {a : α} : Decidable (a ∈ m) :=
  inferInstanceAs (Decidable (a ∈ m.indices))

@[local grind =] private theorem mem_indices_of_mem {m : IndexMap α β} {a : α} :
    a ∈ m ↔ a ∈ m.indices := Iff.rfl

@[inline] def findIdx? (m : IndexMap α β) (a : α) : Option Nat := m.indices[a]?

@[inline] def findIdx (m : IndexMap α β) (a : α) (h : a ∈ m := by get_elem_tactic) : Nat := m.indices[a]

@[inline] def getIdx? (m : IndexMap α β) (i : Nat) : Option β := m.values[i]?

@[inline] def getIdx (m : IndexMap α β) (i : Nat) (h : i < m.size := by get_elem_tactic) : β :=
  m.values[i]

variable [LawfulBEq α] [LawfulHashable α]

local grind_pattern IndexMap.WF1 => self.keys[i]
local grind_pattern IndexMap.WF2 => self.indices[a]
attribute [local grind ←] IndexMap.WF3
attribute [local grind ←] IndexMap.WF4

private theorem getElem_indices_lt {h : a ∈ m} : m.indices[a] < m.size := by
  have : m.indices[a]? = some m.indices[a] := by grind
  grind

grind_pattern getElem_indices_lt => m.indices[a]

attribute [local grind] size

instance : GetElem? (IndexMap α β) α β (fun m a => a ∈ m) where
  getElem m a h := m.values[m.indices[a]'h]
  getElem? m a := m.indices[a]?.bind (fun i => (m.values[i]?))
  getElem! m a := m.indices[a]?.bind (fun i => (m.values[i]?)) |>.getD default

@[local grind =] private theorem getElem_def (m : IndexMap α β) (a : α) (h : a ∈ m) : m[a] = m.values[m.indices[a]'h] := rfl
@[local grind =] private theorem getElem?_def (m : IndexMap α β) (a : α) :
    m[a]? = m.indices[a]?.bind (fun i => (m.values[i]?)) := rfl
@[local grind =] private theorem getElem!_def [Inhabited β] (m : IndexMap α β) (a : α) :
    m[a]! = (m.indices[a]?.bind (fun i => (m.values[i]?))).getD default := rfl

instance : LawfulGetElem (IndexMap α β) α β (fun m a => a ∈ m) where
  getElem?_def := by grind
  getElem!_def := by grind

@[inline] def insert [LawfulBEq α] (m : IndexMap α β) (a : α) (b : β) :
    IndexMap α β :=
  match h : m.indices[a]? with
  | some i =>
    { indices := m.indices
      keys := m.keys.set i a
      values := m.values.set i b }
  | none =>
    { indices := m.indices.insert a m.size
      keys := m.keys.push a
      values := m.values.push b }

instance [LawfulBEq α] : Singleton (α × β) (IndexMap α β) :=
    ⟨fun ⟨a, b⟩ => (∅ : IndexMap α β).insert a b⟩

instance [LawfulBEq α] : Insert (α × β) (IndexMap α β) :=
    ⟨fun ⟨a, b⟩ s => s.insert a b⟩

instance [LawfulBEq α] : LawfulSingleton (α × β) (IndexMap α β) :=
    ⟨fun _ => rfl⟩

@[local grind .] private theorem WF' (i : Nat) (a : α) (h₁ : i < m.keys.size) (h₂ : a ∈ m) :
    m.keys[i] = a ↔ m.indices[a] = i := by
  grind

/--
Erase the key-value pair with the given key, moving the last pair into its place in the order.
If the key is not present, the map is unchanged.
-/
@[inline] def eraseSwap (m : IndexMap α β) (a : α) : IndexMap α β :=
  match h : m.indices[a]? with
  | some i =>
    if w : i = m.size - 1 then
      { indices := m.indices.erase a
        keys := m.keys.pop
        values := m.values.pop }
    else
      let lastKey := m.keys.back
      let lastValue := m.values.back
      { indices := (m.indices.erase a).insert lastKey i
        keys := m.keys.pop.set i lastKey
        values := m.values.pop.set i lastValue }
  | none => m

/-! ### Verification theorems -/

attribute [local grind] getIdx findIdx insert

/--
info: Try these:
  [apply] instantiate only [getIdx, findIdx, = getElem_def]
  [apply] finish only [getIdx, findIdx, = getElem_def]
-/
#guard_msgs in
example (m : IndexMap α β) (a : α) (h : a ∈ m) :
    m.getIdx (m.findIdx a) = m[a] := by
  grind => finish?

example (m : IndexMap α β) (a : α) (h : a ∈ m) :
    m.getIdx (m.findIdx a) = m[a] := by
  grind => instantiate only [getIdx, findIdx, = getElem_def]

/--
info: Try these:
  [apply] ⏎
    instantiate only [= mem_indices_of_mem, insert]
    instantiate only [=_ HashMap.contains_iff_mem, = getElem?_neg, = getElem?_pos]
    cases #bd4f
    · cases #f969
      · instantiate only
      · instantiate only
        instantiate only [= HashMap.contains_insert]
    · cases #2eb4
      · cases #cc2e
        · instantiate only
        · instantiate only
          instantiate only [= HashMap.contains_insert]
      · cases #f969
        · instantiate only
        · instantiate only
          instantiate only [= HashMap.contains_insert]
  [apply] finish only [= mem_indices_of_mem, insert, =_ HashMap.contains_iff_mem, = getElem?_neg, = getElem?_pos,
    = HashMap.contains_insert, #bd4f, #f969, #2eb4, #cc2e]
-/
#guard_msgs in
example (m : IndexMap α β) (a a' : α) (b : β) :
    a' ∈ m.insert a b ↔ a' = a ∨ a' ∈ m := by
  grind => finish?

/--
info: Try these:
  [apply] ⏎
    instantiate only [= mem_indices_of_mem, insert]
    instantiate only [=_ HashMap.contains_iff_mem, = getElem?_neg, = getElem?_pos]
    cases #bd4f
    · cases #f969
      · instantiate only
      · instantiate only
        instantiate only [= HashMap.contains_insert]
    · cases #2eb4
      · cases #cc2e
        · instantiate only
        · instantiate only
          instantiate only [= HashMap.contains_insert]
      · cases #f969
        · instantiate only
        · instantiate only
          instantiate only [= HashMap.contains_insert]
  [apply] finish only [= mem_indices_of_mem, insert, =_ HashMap.contains_iff_mem, = getElem?_neg, = getElem?_pos,
    = HashMap.contains_insert, #bd4f, #f969, #2eb4, #cc2e]
-/
#guard_msgs in
example (m : IndexMap α β) (a a' : α) (b : β) :
    a' ∈ m.insert a b ↔ a' = a ∨ a' ∈ m := by
  grind => finish?

example (m : IndexMap α β) (a a' : α) (b : β) :
    a' ∈ m.insert a b ↔ a' = a ∨ a' ∈ m := by
  grind =>
    instantiate only [= mem_indices_of_mem, insert]
    instantiate only [=_ HashMap.contains_iff_mem, = getElem?_neg, = getElem?_pos]
    cases #bd4f
    · cases #f969
      · instantiate only
      · instantiate only
        instantiate only [= HashMap.contains_insert]
    · cases #2eb4
      · cases #cc2e
        · instantiate only
        · instantiate only
          instantiate only [= HashMap.contains_insert]
      · cases #f969
        · instantiate only
        · instantiate only
          instantiate only [= HashMap.contains_insert]

example (m : IndexMap α β) (a a' : α) (b : β) :
    a' ∈ m.insert a b ↔ a' = a ∨ a' ∈ m := by
  grind =>
    instantiate only [= mem_indices_of_mem, insert]
    instantiate only [=_ HashMap.contains_iff_mem, = getElem?_neg, = getElem?_pos]
    cases #bd4f
    · cases #f969
      · instantiate only
      · instantiate only
        instantiate only [= HashMap.contains_insert]
    · cases #2eb4
      · cases #cc2e
        · instantiate only
        · instantiate only
          instantiate only [= HashMap.contains_insert]
      · cases #f969
        · instantiate only
        · instantiate only
          instantiate only [= HashMap.contains_insert]

/--
info: Try these:
  [apply] ⏎
    instantiate only [= mem_indices_of_mem, insert, = getElem_def]
    instantiate only [= getElem?_neg, = getElem?_pos]
    cases #dbaf
    · cases #f969
      · instantiate only
        instantiate only [= Array.getElem_set]
      · instantiate only
        instantiate only [size, = HashMap.mem_insert, = HashMap.getElem_insert, = Array.getElem_push]
    · instantiate only [= mem_indices_of_mem, = getElem_def]
      instantiate only [usr getElem_indices_lt, usr WF2]
      instantiate only [size, ← WF3]
      cases #f969
      · instantiate only [WF']
        instantiate only [= Array.getElem_set]
      · instantiate only
        instantiate only [= HashMap.mem_insert, = HashMap.getElem_insert, = Array.getElem_push]
  [apply] finish only [= mem_indices_of_mem, insert, = getElem_def, = getElem?_neg, = getElem?_pos, = Array.getElem_set,
    size, = HashMap.mem_insert, = HashMap.getElem_insert, = Array.getElem_push, usr getElem_indices_lt, usr WF2, ← WF3,
    WF', #dbaf, #f969]
-/
#guard_msgs in
example (m : IndexMap α β) (a a' : α) (b : β) (h : a' ∈ m.insert a b) :
    (m.insert a b)[a'] = if h' : a' == a then b else m[a'] := by
  grind => finish?

example (m : IndexMap α β) (a a' : α) (b : β) (h : a' ∈ m.insert a b) :
    (m.insert a b)[a'] = if h' : a' == a then b else m[a'] := by
  grind => 
    instantiate only [= mem_indices_of_mem, insert, = getElem_def]
    instantiate only [= getElem?_neg, = getElem?_pos]
    cases #dbaf
    · cases #f969
      · instantiate only
        instantiate only [= Array.getElem_set]
      · instantiate only
        instantiate only [size, = HashMap.mem_insert, = HashMap.getElem_insert,
          = Array.getElem_push]
    · instantiate only [= mem_indices_of_mem, = getElem_def]
      instantiate only [usr getElem_indices_lt, usr WF2]
      instantiate only [size, ← WF3]
      cases #f969
      · instantiate only [WF']
        instantiate only [= Array.getElem_set]
      · instantiate only
        instantiate only [= HashMap.mem_insert, = HashMap.getElem_insert, = Array.getElem_push]

/--
info: Try these:
  [apply] grind only [= mem_indices_of_mem, insert, = getElem_def, = getElem?_neg, = getElem?_pos, = Array.getElem_set,
    size, = HashMap.mem_insert, = HashMap.getElem_insert, = Array.getElem_push, usr getElem_indices_lt, usr WF2, ← WF3,
    WF', #dbaf, #f969]
  [apply] grind only [= mem_indices_of_mem, insert, = getElem_def, = getElem?_neg, = getElem?_pos, = Array.getElem_set,
    size, = HashMap.mem_insert, = HashMap.getElem_insert, = Array.getElem_push, usr getElem_indices_lt, usr WF2, ← WF3,
    WF']
  [apply] grind =>
    instantiate only [= mem_indices_of_mem, insert, = getElem_def]
    instantiate only [= getElem?_neg, = getElem?_pos]
    cases #dbaf
    · cases #f969
      · instantiate only
        instantiate only [= Array.getElem_set]
      · instantiate only
        instantiate only [size, = HashMap.mem_insert, = HashMap.getElem_insert, = Array.getElem_push]
    · instantiate only [= mem_indices_of_mem, = getElem_def]
      instantiate only [usr getElem_indices_lt, usr WF2]
      instantiate only [size, ← WF3]
      cases #f969
      · instantiate only [WF']
        instantiate only [= Array.getElem_set]
      · instantiate only
        instantiate only [= HashMap.mem_insert, = HashMap.getElem_insert, = Array.getElem_push]
-/
#guard_msgs in
example (m : IndexMap α β) (a a' : α) (b : β) (h : a' ∈ m.insert a b) :
    (m.insert a b)[a'] = if h' : a' == a then b else m[a'] := by
  grind?

example (m : IndexMap α β) (a a' : α) (b : β) (h : a' ∈ m.insert a b) :
    (m.insert a b)[a'] = if h' : a' == a then b else m[a'] := by
  grind =>
    instantiate only [= mem_indices_of_mem, insert, = getElem_def]
    instantiate only [= getElem?_neg, = getElem?_pos]
    cases #dbaf
    · cases #f969
      · instantiate only
        instantiate only [= Array.getElem_set]
      · instantiate only
        instantiate only [size, = HashMap.mem_insert, = HashMap.getElem_insert,
          = Array.getElem_push]
    · instantiate only [= mem_indices_of_mem, = getElem_def]
      instantiate only [usr getElem_indices_lt, usr WF2]
      instantiate only [size, ← WF3]
      cases #f969
      · instantiate only [WF']
        instantiate only [= Array.getElem_set]
      · instantiate only
        instantiate only [= HashMap.mem_insert, = HashMap.getElem_insert, = Array.getElem_push]

example (m : IndexMap α β) (a a' : α) (b : β) (h : a' ∈ m.insert a b) :
    (m.insert a b)[a'] = if h' : a' == a then b else m[a'] := by
  grind only [= mem_indices_of_mem, insert, = getElem_def, = getElem?_neg, = getElem?_pos,
    = Array.getElem_set, size, = HashMap.mem_insert, = HashMap.getElem_insert, = Array.getElem_push,
    usr getElem_indices_lt, usr WF2, ← WF3, WF', #dbaf, #f969]

/--
info: Try these:
  [apply] ⏎
    instantiate only [findIdx, insert, = mem_indices_of_mem]
    instantiate only [= getElem?_neg, = getElem?_pos]
    cases #ffde
    · instantiate only [findIdx]
    · instantiate only
      instantiate only [= HashMap.mem_insert, = HashMap.getElem_insert]
  [apply] finish only [findIdx, insert, = mem_indices_of_mem, = getElem?_neg, = getElem?_pos, = HashMap.mem_insert,
    = HashMap.getElem_insert, #ffde]
-/
#guard_msgs in
example (m : IndexMap α β) (a : α) (b : β) :
    (m.insert a b).findIdx a = if h : a ∈ m then m.findIdx a else m.size := by
  grind => finish?

/--
info: Try these:
  [apply] grind
  [apply] grind only [findIdx, insert, = mem_indices_of_mem, = getElem?_neg, = getElem?_pos, = HashMap.mem_insert,
    = HashMap.getElem_insert, #ffde]
  [apply] grind only [findIdx, insert, = mem_indices_of_mem, = getElem?_neg, = getElem?_pos, = HashMap.mem_insert,
    = HashMap.getElem_insert]
  [apply] grind =>
    instantiate only [findIdx, insert, = mem_indices_of_mem]
    instantiate only [= getElem?_neg, = getElem?_pos]
    cases #ffde
    · instantiate only [findIdx]
    · instantiate only
      instantiate only [= HashMap.mem_insert, = HashMap.getElem_insert]
-/
#guard_msgs in
example (m : IndexMap α β) (a : α) (b : β) :
    (m.insert a b).findIdx a = if h : a ∈ m then m.findIdx a else m.size := by
  try?

example (m : IndexMap α β) (a : α) (b : β) :
    (m.insert a b).findIdx a = if h : a ∈ m then m.findIdx a else m.size := by
  grind => finish?

example (m : IndexMap α β) (a : α) (b : β) :
    (m.insert a b).findIdx a = if h : a ∈ m then m.findIdx a else m.size := by
  grind =>
    instantiate only [findIdx, insert, = mem_indices_of_mem]
    instantiate only [= getElem?_neg, = getElem?_pos]
    cases #acc3
    · instantiate only [findIdx]
    · finish only [= HashMap.mem_insert, = HashMap.getElem_insert]

example (m : IndexMap α β) (a : α) (b : β) :
    (m.insert a b).findIdx a = if h : a ∈ m then m.findIdx a else m.size := by
  grind =>
    instantiate only [findIdx, insert, = mem_indices_of_mem]
    instantiate only [= getElem?_neg, = getElem?_pos]
    cases #acc3 <;>
      finish only [findIdx, = HashMap.mem_insert, = HashMap.getElem_insert]

end IndexMap
