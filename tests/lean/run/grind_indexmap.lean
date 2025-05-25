import Std.Data.HashMap

set_option grind.warning false

macro_rules | `(tactic| get_elem_tactic_trivial) => `(tactic| grind)

attribute [grind] Array.emptyWithCapacity_eq

open Std

structure IndexMap (α : Type u) (β : Type v) [BEq α] [Hashable α] where
  indices : HashMap α Nat
  data : Array (α × β)
  WF : ∀ (a : α) (b : β) (i : Nat), data[i]? = some (a, b) ↔ indices[a]? = some i := by grind

namespace IndexMap

variable {α : Type u} {β : Type v} [BEq α] [LawfulBEq α] [Hashable α] [LawfulHashable α]
variable {m : IndexMap α β} {a : α} {b : β} {i : Nat}

@[inline] def size (m : IndexMap α β) : Nat :=
  m.data.size

def emptyWithCapacity (capacity := 8) : IndexMap α β where
  indices := HashMap.emptyWithCapacity capacity
  data := Array.emptyWithCapacity capacity

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

example (m : HashMap α β) (h : m[a]? = some b) : a ∈ m := by grind
example (m : HashMap α β) (h : m[a]? = some b) : m[a] = b := by grind
example (m : HashMap α β) : m[a]? = some b ↔ ∃ h, m[a] = b := by
  -- grind [of_getElem?_eq_some]
  exact HashMap.getElem?_eq_some_iff

instance : GetElem? (IndexMap α β) α β (fun m a => a ∈ m) where
  getElem m a h := m.data[m.indices[a]'h].2
  getElem? m a := m.indices[a]?.pbind fun i h => (m.data[i]'(by sorry)).2
  getElem! m a := m.indices[a]?.bind (fun i => m.data[i]?) |>.map (·.2) |>.getD default

@[local grind] private theorem getElem_def (m : IndexMap α β) (a : α) (h : a ∈ m) : m[a] = m.data[m.indices[a]'h].2 := rfl
@[local grind] private theorem getElem?_def (m : IndexMap α β) (a : α) :
    m[a]? = m.indices[a]?.pbind fun i h => (m.data[i]'(by sorry)).2 := rfl

@[local grind] private theorem getElem_data_getElem_indices
   {m : IndexMap α β} {a : α} {h : a ∈ m} :
   m.data[m.indices[a]'h] = (a, m[a]) := sorry

@[local grind] private theorem mem_indices_of_mem {m : IndexMap α β} {a : α} :
    a ∈ m ↔ a ∈ m.indices := Iff.rfl

instance : LawfulGetElem (IndexMap α β) α β (fun m a => a ∈ m) where
  getElem?_def := by
    -- Lots of problems here!
    -- several occurrences of `type error constructing proof for`
    -- there are also a number of repetitions in the equivalence classes.
    grind [getElem?_pos]
  getElem!_def := sorry

@[inline] def findIdx? (m : IndexMap α β) (a : α) : Option Nat := m.indices[a]?

@[inline] def findIdx (m : IndexMap α β) (a : α) (h : a ∈ m) : Nat := m.indices[a]

@[inline] def getIdx? (m : IndexMap α β) (i : Nat) : Option β := m.data[i]?.map (·.2)

@[inline] def getIdx (m : IndexMap α β) (i : Nat) (h : i < m.size) : β := m.data[i].2

@[inline] def insert (m : IndexMap α β) (a : α) (b : β) : IndexMap α β :=
  match h : m.indices[a]? with
  | some i =>
    { m with
      data := m.data.set i (a, b) sorry
      WF := sorry }
  | none =>
    { m with
      indices := m.indices.insert a m.size
      data := m.data.push (a, b)
      WF := sorry }

instance : Singleton (α × β) (IndexMap α β) := ⟨fun ⟨a, b⟩ => (∅ : IndexMap α β).insert a b⟩

instance : Insert (α × β) (IndexMap α β) := ⟨fun ⟨a, b⟩ s => s.insert a b⟩

instance : LawfulSingleton (α × β) (IndexMap α β) := ⟨fun _ => rfl⟩

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
