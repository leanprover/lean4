import Std.Data.HashMap

macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| grind)

open Std

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

attribute [local grind _=_] IndexMap.WF

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
  have := m.WF i a
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
info: Try this:
  [apply] instantiate only [getIdx, findIdx, = getElem_def]
-/
#guard_msgs in
example (m : IndexMap α β) (a : α) (h : a ∈ m) :
    m.getIdx (m.findIdx a) = m[a] := by
  grind => finish?

example (m : IndexMap α β) (a : α) (h : a ∈ m) :
    m.getIdx (m.findIdx a) = m[a] := by
  grind => instantiate only [getIdx, findIdx, = getElem_def]

/--
info: Try this:
  [apply] ⏎
    instantiate only [= mem_indices_of_mem, insert]
    instantiate only [=_ HashMap.contains_iff_mem, = getElem?_neg, = getElem?_pos]
    instantiate only [=_ HashMap.contains_iff_mem]
    cases #4ed2
    next =>
      cases #ffdf
      next => instantiate only
      next =>
        instantiate only
        instantiate only [= HashMap.contains_insert]
    next =>
      cases #95a0
      next =>
        cases #2688
        next => instantiate only
        next =>
          instantiate only
          instantiate only [= HashMap.contains_insert]
      next =>
        cases #ffdf
        next => instantiate only
        next =>
          instantiate only
          instantiate only [= HashMap.contains_insert]
-/
#guard_msgs in
example (m : IndexMap α β) (a a' : α) (b : β) :
    a' ∈ m.insert a b ↔ a' = a ∨ a' ∈ m := by
  grind => finish?

-- **TODO**: Investigate whey the following `finish?` has one fewer step.
/--
info: Try this:
  [apply] ⏎
    instantiate only [= mem_indices_of_mem, insert]
    instantiate only [=_ HashMap.contains_iff_mem, = getElem?_neg, = getElem?_pos]
    cases #4ed2
    next =>
      cases #ffdf
      next => instantiate only
      next =>
        instantiate only
        instantiate only [= HashMap.contains_insert]
    next =>
      cases #95a0
      next =>
        cases #2688
        next => instantiate only
        next =>
          instantiate only
          instantiate only [= HashMap.contains_insert]
      next =>
        cases #ffdf
        next => instantiate only
        next =>
          instantiate only
          instantiate only [= HashMap.contains_insert]
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
    cases #4ed2
    next =>
      cases #ffdf
      next => instantiate only
      next =>
        instantiate only
        instantiate only [= HashMap.contains_insert]
    next =>
      cases #95a0
      next =>
        cases #2688
        next => instantiate only
        next =>
          instantiate only
          instantiate only [= HashMap.contains_insert]
      next =>
        cases #ffdf
        next => instantiate only
        next =>
          instantiate only
          instantiate only [= HashMap.contains_insert]

/--
info: Try this:
  [apply] ⏎
    instantiate approx [= getElem_def, = mem_indices_of_mem, insert]
    instantiate only [= getElem?_neg, = getElem?_pos]
    cases #f590
    next =>
      cases #ffdf
      next =>
        instantiate only
        instantiate only [= Array.getElem_set]
      next =>
        instantiate only
        instantiate only [= Array.getElem_push, size, = HashMap.getElem_insert, = HashMap.mem_insert]
    next =>
      instantiate only [= getElem_def, = mem_indices_of_mem]
      instantiate only [usr getElem_indices_lt]
      instantiate only [size]
      cases #ffdf
      next =>
        instantiate only [=_ WF]
        instantiate only [= Array.getElem_set, = getElem?_neg, = getElem?_pos]
        instantiate only [WF']
      next =>
        instantiate only
        instantiate only [= Array.getElem_push, = HashMap.mem_insert, = HashMap.getElem_insert]
-/
#guard_msgs in
example (m : IndexMap α β) (a a' : α) (b : β) (h : a' ∈ m.insert a b) :
    (m.insert a b)[a'] = if h' : a' == a then b else m[a'] := by
  grind => finish?

example (m : IndexMap α β) (a a' : α) (b : β) (h : a' ∈ m.insert a b) :
    (m.insert a b)[a'] = if h' : a' == a then b else m[a'] := by
  grind =>
    -- **TODO**: Check approx here
    instantiate approx [= getElem_def, = mem_indices_of_mem, insert]
    instantiate only [= getElem?_neg, = getElem?_pos]
    cases #f590
    next =>
      cases #ffdf
      next =>
        instantiate only
        instantiate only [= Array.getElem_set]
      next =>
        instantiate only
        instantiate only [= Array.getElem_push, size, = HashMap.getElem_insert,
          = HashMap.mem_insert]
    next =>
      instantiate only [= getElem_def, = mem_indices_of_mem]
      instantiate only [usr getElem_indices_lt]
      instantiate only [size]
      cases #ffdf
      next =>
        instantiate only [=_ WF]
        instantiate only [= Array.getElem_set, = getElem?_neg, = getElem?_pos]
        instantiate only [WF']
      next =>
        instantiate only
        instantiate only [= Array.getElem_push, = HashMap.mem_insert, = HashMap.getElem_insert]

/--
info: Try this:
  [apply] ⏎
    instantiate only [insert, = mem_indices_of_mem, findIdx]
    instantiate only [= getElem?_pos, = getElem?_neg]
    cases #1bba
    next => instantiate only [findIdx]
    next =>
      instantiate only
      instantiate only [= HashMap.mem_insert, = HashMap.getElem_insert]
-/
#guard_msgs in
example (m : IndexMap α β) (a : α) (b : β) :
    (m.insert a b).findIdx a = if h : a ∈ m then m.findIdx a else m.size := by
  grind => finish?

example (m : IndexMap α β) (a : α) (b : β) :
    (m.insert a b).findIdx a = if h : a ∈ m then m.findIdx a else m.size := by
  grind =>
    instantiate only [insert, = mem_indices_of_mem, findIdx]
    instantiate only [= getElem?_pos, = getElem?_neg]
    cases #1bba
    next => instantiate only [findIdx]
    next =>
      instantiate only
      instantiate only [= HashMap.mem_insert, = HashMap.getElem_insert]

end IndexMap
