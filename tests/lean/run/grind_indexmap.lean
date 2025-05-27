import Std.Data.HashMap

set_option grind.warning false

macro_rules | `(tactic| get_elem_tactic_trivial) => `(tactic| grind)

attribute [grind] Array.emptyWithCapacity_eq

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

private theorem getElem_indices_lt {h : a ∈ m} : m.indices[a] < m.size := by sorry

grind_pattern getElem_indices_lt => m.indices[a]

attribute [local grind] size

-- variable [LawfulBEq α] [LawfulHashable α]

-- example (m : HashMap α β) (h : m[a]? = some b) : a ∈ m := by grind
-- example (m : HashMap α β) (h : m[a]? = some b) : m[a] = b := by grind
-- example (m : HashMap α β) : m[a]? = some b ↔ ∃ h, m[a] = b := by grind [getElem?_pos]

instance : GetElem? (IndexMap α β) α β (fun m a => a ∈ m) where
  getElem m a h := m.values[m.indices[a]'h]
  getElem? m a := m.indices[a]?.bind (fun i => (m.values[i]?))
  getElem! m a := m.indices[a]?.bind (fun i => (m.values[i]?)) |>.getD default

@[local grind] private theorem getElem_def (m : IndexMap α β) (a : α) (h : a ∈ m) : m[a] = m.values[m.indices[a]'h] := rfl
@[local grind] private theorem getElem?_def (m : IndexMap α β) (a : α) :
    m[a]? = m.indices[a]?.bind (fun i => (m.values[i]?)) := rfl
@[local grind] private theorem getElem!_def [Inhabited β] (m : IndexMap α β) (a : α) :
    m[a]! = (m.indices[a]?.bind (fun i => (m.values[i]?)) |>.getD default) := rfl

@[local grind] private theorem getElem_keys_getElem_indices
    {m : IndexMap α β} {a : α} {h : a ∈ m} :
  m.keys[m.indices[a]'h] = a := sorry

@[local grind] private theorem mem_indices_of_mem {m : IndexMap α β} {a : α} :
    a ∈ m ↔ a ∈ m.indices := Iff.rfl

variable [LawfulBEq α] [LawfulHashable α]

instance : LawfulGetElem (IndexMap α β) α β (fun m a => a ∈ m) where
  getElem?_def := by grind [getElem?_pos]
  getElem!_def := by grind [getElem!_pos]

@[inline] def findIdx? (m : IndexMap α β) (a : α) : Option Nat := m.indices[a]?

@[inline] def findIdx (m : IndexMap α β) (a : α) (h : a ∈ m) : Nat := m.indices[a]

@[inline] def getIdx? (m : IndexMap α β) (i : Nat) : Option β := m.values[i]?

@[inline] def getIdx (m : IndexMap α β) (i : Nat) (h : i < m.size) : β := m.values[i]

-- attribute [local grind?] IndexMap.WF -- Hmm, I'm not convinced about the pattern for this one.

-- @[local grind →] private theorem size_data_lt_of_getElem_indices (h : m.indices[a]? = some i) :
--     i < m.data.size := sorry
-- @[local grind →] private theorem getElem_keys_of_getElem_indices (h : m.indices[a]? = some i) :
--     m.keys[i] = a := sorry

-- Equivalent to the pair below, no?
attribute [local grind? _=_] IndexMap.WF

-- @[local grind →] private theorem getElem?_indices_of_getElem?_keys (g : m.keys[i]? = some a) :
--     m.indices[a]? = some i := sorry
-- @[local grind →] private theorem getElem?_keys?_of_getElem?_indices (h : m.indices[a]? = some i) :
--     m.keys[i]? = some a := sorry

attribute [grind =] Array.getElem?_push

@[inline] def insert (m : IndexMap α β) (a : α) (b : β) : IndexMap α β :=
  match h : m.indices[a]? with
  | some i =>
    { indices := m.indices
      keys := m.keys.set i a (by grind)
      values := m.values.set i b (by grind) }
  | none =>
    { indices := m.indices.insert a m.size
      keys := m.keys.push a
      values := m.values.push b
      WF := by
        intro j b
        rw [HashMap.getElem?_insert]
        constructor
        · intro w
          fail_if_success grind (gen := 6) -- This fails, but `split <;> grind` is fine?
          split <;> grind
        · intro w
          rw [Array.getElem?_push]
          split <;> rename_i h'
          · subst h'
            split at w <;> grind
          · grind
         }

instance : Singleton (α × β) (IndexMap α β) := ⟨fun ⟨a, b⟩ => (∅ : IndexMap α β).insert a b⟩

instance : Insert (α × β) (IndexMap α β) := ⟨fun ⟨a, b⟩ s => s.insert a b⟩

instance : LawfulSingleton (α × β) (IndexMap α β) := ⟨fun _ => rfl⟩

#exit

/--
Erase the key-value pair with the given key, moving the last pair into its place in the order.
If the key is not present, the map is unchanged.
-/
@[inline] def eraseSwap (m : IndexMap α β) (a : α) : IndexMap α β :=
  match h : m.indices[a]? with
  | some i =>
    let last := m.data.back sorry
    { m with
      indices := (m.indices.erase a).insert last.1 i
      data := m.data.set i last sorry
      WF := sorry }
  | none => m

/-! ### Verification theorems -/

theorem getIdx_findIdx (m : IndexMap α β) (a : α) (h : a ∈ m) :
    m.getIdx (m.findIdx a h) sorry = m[a] :=
  sorry

theorem getElem_insert (m : IndexMap α β) (a a' : α) (b : β) (h) :
    (m.insert a b)[a']'h = if h' : a' == a then b else m[a']'(sorry) := by
  sorry

theorem findIdx_insert_self (m : IndexMap α β) (a : α) (b : β) :
    (m.insert a b).findIdx a sorry = if h : a ∈ m then m.findIdx a h else m.size := by
  sorry

end IndexMap
