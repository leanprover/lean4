module
-- This is a companion file for `grind_indexmap.lean`,
-- showing what an outline of this file might look like before any proofs are written.

import Std.Data.HashMap

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
  private size_keys' : keys.size = values.size
  private WF : ∀ (i : Nat) (a : α), keys[i]? = some a ↔ indices[a]? = some i

namespace IndexMap

variable {α : Type u} {β : Type v} [BEq α] [Hashable α]
variable {m : IndexMap α β} {a : α} {b : β} {i : Nat}

@[inline] def size (m : IndexMap α β) : Nat :=
  m.values.size

def emptyWithCapacity (capacity := 8) : IndexMap α β where
  indices := HashMap.emptyWithCapacity capacity
  keys    := Array.emptyWithCapacity capacity
  values  := Array.emptyWithCapacity capacity
  size_keys' := sorry
  WF := sorry

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

@[inline] def findIdx? (m : IndexMap α β) (a : α) : Option Nat := m.indices[a]?

@[inline] def findIdx (m : IndexMap α β) (a : α) (h : a ∈ m := by get_elem_tactic) : Nat := m.indices[a]

@[inline] def getIdx? (m : IndexMap α β) (i : Nat) : Option β := m.values[i]?

@[inline] def getIdx (m : IndexMap α β) (i : Nat) (h : i < m.size := by get_elem_tactic) : β :=
  m.values[i]

variable [LawfulBEq α] [LawfulHashable α]

instance : GetElem? (IndexMap α β) α β (fun m a => a ∈ m) where
  getElem m a h := m.values[m.indices[a]'h]'(by sorry)
  getElem? m a  := m.indices[a]?.bind (fun i => (m.values[i]?))
  getElem! m a  := m.indices[a]?.bind (fun i => (m.values[i]?)) |>.getD default

instance : LawfulGetElem (IndexMap α β) α β (fun m a => a ∈ m) where
  getElem?_def := sorry
  getElem!_def := sorry

@[inline] def insert (m : IndexMap α β) (a : α) (b : β) : IndexMap α β :=
  match h : m.indices[a]? with
  | some i =>
    { indices := m.indices
      keys    := m.keys.set i a sorry
      values  := m.values.set i b sorry
      size_keys' := sorry
      WF      := sorry }
  | none =>
    { indices := m.indices.insert a m.size
      keys    := m.keys.push a
      values  := m.values.push b
      size_keys' := sorry
      WF      := sorry }

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
        values  := m.values.pop
        size_keys' := sorry
        WF := sorry }
    else
      let lastKey := m.keys.back sorry
      let lastValue := m.values.back sorry
      { indices := (m.indices.erase a).insert lastKey i
        keys    := m.keys.pop.set i lastKey sorry
        values  := m.values.pop.set i lastValue sorry
        size_keys' := sorry
        WF := sorry }
  | none => m

-- TODO: similarly define `eraseShift`, etc.

/-! ### Verification theorems (not exhaustive) -/

theorem mem_insert (m : IndexMap α β) (a a' : α) (b : β) :
    a' ∈ m.insert a b ↔ a' = a ∨ a' ∈ m := by
  sorry

theorem getElem_insert (m : IndexMap α β) (a a' : α) (b : β) (h : a' ∈ m.insert a b) :
    (m.insert a b)[a']'h = if h' : a' == a then b else m[a']'sorry := by
  sorry

theorem findIdx_lt (m : IndexMap α β) (a : α) (h : a ∈ m) :
    m.findIdx a h < m.size := by
  sorry

theorem findIdx_insert_self (m : IndexMap α β) (a : α) (b : β) :
    (m.insert a b).findIdx a sorry = if h : a ∈ m then m.findIdx a h else m.size := by
  sorry

theorem findIdx?_eq (m : IndexMap α β) (a : α) :
    m.findIdx? a = if h : a ∈ m then some (m.findIdx a h) else none := by
  sorry

theorem getIdx_findIdx (m : IndexMap α β) (a : α) (h : a ∈ m) :
    m.getIdx (m.findIdx a h) sorry = m[a] := sorry

theorem getIdx?_eq (m : IndexMap α β) (i : Nat) :
    m.getIdx? i = if h : i < m.size then some (m.getIdx i h) else none := sorry

theorem getElem?_eraseSwap (m : IndexMap α β) (a a' : α) :
    (m.eraseSwap a)[a']? = if a' == a then none else m[a']? := sorry

theorem mem_eraseSwap (m : IndexMap α β) (a a' : α) :
    a' ∈ m.eraseSwap a ↔ a' ≠ a ∧ a' ∈ m := sorry

theorem getElem_eraseSwap (m : IndexMap α β) (a a' : α) (h : a' ∈ m.eraseSwap a) :
    (m.eraseSwap a)[a'] = m[a']'sorry := sorry

end IndexMap
