module
-- See also the companion file `grind_indexmap_pre.lean`,
-- showing this file might have looked like before any proofs are written.
-- This file fills them all in with `grind`!

import Std.Data.HashMap
import Lean.LibrarySuggestions.Default

local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| grind)

open Std

/--
An `IndexMap α β` is a map from keys of type `α` to values of type `β`,
which also maintains the insertion order of keys.

Internally `IndexMap` is implementented redundantly as a `HashMap` from keys to indices
(and hence the key type must be `Hashable`), along with `Array`s of keys and values.
These implementation details are private, and hidden from the user.
-/
structure IndexMap (α : Type u) (β : Type v) [BEq α] [Hashable α] where
  private indices : HashMap α Nat
  private keys : Array α
  private values : Array β
  private size_keys' : keys.size = values.size := by grind
  private WF : ∀ (i : Nat) (a : α), keys[i]? = some a ↔ indices[a]? = some i := by grind

namespace IndexMap

variable {α : Type u} {β : Type v} [BEq α] [Hashable α]
variable {m : IndexMap α β} {a : α} {b : β} {i : Nat}

@[inline] def size (m : IndexMap α β) : Nat :=
  m.values.size

@[local grind =]
private theorem size_keys : m.keys.size = m.size := size_keys' _

@[local grind =]
private theorem size_values : m.values.size = m.size := rfl

def emptyWithCapacity (capacity := 8) : IndexMap α β where
  indices := HashMap.emptyWithCapacity capacity
  keys    := Array.emptyWithCapacity capacity
  values  := Array.emptyWithCapacity capacity

instance : EmptyCollection (IndexMap α β) where
  emptyCollection := emptyWithCapacity

instance : Inhabited (IndexMap α β) where
  default := ∅

@[inline] def contains (m : IndexMap α β) (a : α) : Bool :=
  m.indices.contains a

instance : Membership α (IndexMap α β) where
  mem m a := a ∈ m.indices

instance {m : IndexMap α β} {a : α} : Decidable (a ∈ m) :=
  inferInstanceAs (Decidable (a ∈ m.indices))

@[local grind _=_]
private theorem mem_indices {m : IndexMap α β} {a : α} :
    a ∈ m.indices ↔ a ∈ m := by rfl

@[inline] def findIdx? (m : IndexMap α β) (a : α) : Option Nat := m.indices[a]?

@[inline] def findIdx (m : IndexMap α β) (a : α) (h : a ∈ m := by get_elem_tactic) : Nat := m.indices[a]

@[inline] def getIdx? (m : IndexMap α β) (i : Nat) : Option β := m.values[i]?

@[inline] def getIdx (m : IndexMap α β) (i : Nat) (h : i < m.size := by get_elem_tactic) : β :=
  m.values[i]

variable [LawfulBEq α] [LawfulHashable α]

attribute [local grind _=_] IndexMap.WF

instance : GetElem? (IndexMap α β) α β (fun m a => a ∈ m) where
  getElem m a h := m.values[m.indices[a]'h]
  getElem? m a  := m.indices[a]?.bind (fun i => (m.values[i]?))
  getElem! m a  := m.indices[a]?.bind (fun i => (m.values[i]?)) |>.getD default

@[local grind =]
private theorem getElem_def (m : IndexMap α β) (a : α) (h : a ∈ m) :
    m[a] = m.values[m.indices[a]'h] := rfl
@[local grind =]
private theorem getElem?_def (m : IndexMap α β) (a : α) :
    m[a]? = m.indices[a]?.bind (fun i => (m.values[i]?)) := rfl
@[local grind =]
private theorem getElem!_def [Inhabited β] (m : IndexMap α β) (a : α) :
    m[a]! = (m.indices[a]?.bind (fun i => (m.values[i]?))).getD default := rfl

instance : LawfulGetElem (IndexMap α β) α β (fun m a => a ∈ m) where
  getElem?_def := by grind
  getElem!_def := by grind

@[inline] def insert (m : IndexMap α β) (a : α) (b : β) : IndexMap α β :=
  match h : m.indices[a]? with
  | some i =>
    { indices := m.indices
      keys    := m.keys.set i a
      values  := m.values.set i b }
  | none =>
    { indices := m.indices.insert a m.size
      keys    := m.keys.push a
      values  := m.values.push b }

instance : Singleton (α × β) (IndexMap α β) :=
  ⟨fun ⟨a, b⟩ => (∅ : IndexMap α β).insert a b⟩

instance : Insert (α × β) (IndexMap α β) :=
  ⟨fun ⟨a, b⟩ s => s.insert a b⟩

instance : LawfulSingleton (α × β) (IndexMap α β) :=
  ⟨fun _ => rfl⟩

/--
Erase the key-value pair with the given key, moving the last pair into its place in the order.
If the key is not present, the map is unchanged.
-/
@[inline] def eraseSwap (m : IndexMap α β) (a : α) : IndexMap α β :=
  match h : m.indices[a]? with
  | some i =>
    if w : i = m.size - 1 then
      { indices := m.indices.erase a
        keys    := m.keys.pop
        values  := m.values.pop }
    else
      let lastKey := m.keys.back
      let lastValue := m.values.back
      { indices := (m.indices.erase a).insert lastKey i
        keys    := m.keys.pop.set i lastKey
        values  := m.values.pop.set i lastValue }
  | none => m

-- TODO: similarly define `eraseShift`, etc.

/-! ### Verification theorems (not exhaustive) -/

@[grind =]
theorem mem_insert (m : IndexMap α β) (a a' : α) (b : β) :
    a' ∈ m.insert a b ↔ a' = a ∨ a' ∈ m := by
  grind +locals

@[grind =]
theorem getElem_insert (m : IndexMap α β) (a a' : α) (b : β) (h : a' ∈ m.insert a b) :
    (m.insert a b)[a'] = if h' : a' == a then b else m[a'] := by
  grind +locals

theorem findIdx_lt (m : IndexMap α β) (a : α) (h : a ∈ m) :
    m.findIdx a h < m.size := by
  grind +locals

grind_pattern findIdx_lt => m.findIdx a h

@[grind =]
theorem findIdx_insert_self (m : IndexMap α β) (a : α) (b : β) :
    (m.insert a b).findIdx a = if h : a ∈ m then m.findIdx a else m.size := by
  grind +locals

@[grind =]
theorem findIdx?_eq (m : IndexMap α β) (a : α) :
    m.findIdx? a = if h : a ∈ m then some (m.findIdx a h) else none := by
  grind +locals

@[grind =]
theorem getIdx_findIdx (m : IndexMap α β) (a : α) (h : a ∈ m) :
    m.getIdx (m.findIdx a) = m[a] := by grind +locals

omit [LawfulBEq α] [LawfulHashable α] in
@[grind =]
theorem getIdx?_eq (m : IndexMap α β) (i : Nat) :
    m.getIdx? i = if h : i < m.size then some (m.getIdx i h) else none := by
  grind +locals

private theorem getElem_keys_mem {m : IndexMap α β} {i : Nat} (h : i < m.size) :
    m.keys[i] ∈ m := by
  have : m.indices[m.keys[i]]? = some i := by grind
  grind

local grind_pattern getElem_keys_mem => m.keys[i]

theorem getElem?_eraseSwap (m : IndexMap α β) (a a' : α) :
    (m.eraseSwap a)[a']? = if a' == a then none else m[a']? := by
  grind +locals

@[grind =]
theorem mem_eraseSwap (m : IndexMap α β) (a a' : α) :
    a' ∈ m.eraseSwap a ↔ a' ≠ a ∧ a' ∈ m := by
  grind +locals

theorem getElem_eraseSwap (m : IndexMap α β) (a a' : α) (h : a' ∈ m.eraseSwap a) :
    (m.eraseSwap a)[a'] = m[a'] := by
  grind +locals

end IndexMap
