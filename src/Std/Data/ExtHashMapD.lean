prelude
import Std.Data.ExtHashMap
import Init.Grind

namespace Std

structure ExtHashMapD (α : Type u) [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α] (β : Type v) [BEq β] [Inhabited β] where
  /-- Internal implementation detail of the hash map -/
  inner : ExtHashMap α β
  /-- None of the values in the hash map are equal to the default value. -/
  get_ne_default : ∀ (x : α) h, inner[x] != default

namespace ExtHashMapD

variable {α : Type u} [BEq α] [LawfulBEq α] [Hashable α] [LawfulHashable α] {β : Type v} [BEq β] [Inhabited β]

@[inline, inherit_doc ExtHashMap.emptyWithCapacity]
def emptyWithCapacity (capacity := 8) : ExtHashMapD α β :=
  ⟨ExtHashMap.emptyWithCapacity capacity, by sorry⟩

instance : EmptyCollection (ExtHashMapD α β) where
  emptyCollection := emptyWithCapacity

instance : Inhabited (ExtHashMapD α β) where
  default := ∅

def set (m : ExtHashMapD α β) (a : α) (b : β) : ExtHashMapD α β :=
  if b == default then ⟨m.inner.erase a, by sorry⟩ else ⟨m.inner.insert a b, by sorry⟩

instance : Singleton (α × β) (ExtHashMapD α β) where
  singleton | ⟨a, b⟩ => (∅ : ExtHashMapD α β).set a b

instance : Insert (α × β) (ExtHashMapD α β) where
  insert | ⟨a, b⟩, s => s.set a b

instance : LawfulSingleton (α × β) (ExtHashMapD α β) :=
  ⟨fun _ => rfl⟩

instance : GetElem (ExtHashMapD α β) α β (fun _ _ => True) where
  getElem m a _ := m.inner.getD a default

def map [BEq γ] [Inhabited γ] (f : α → β → γ) (m : ExtHashMapD α β) : ExtHashMapD α γ :=
  ⟨m.inner.filterMap fun a b => let g := f a b; if g == default then none else some g, by sorry⟩

def insertMany {ρ : Type w}
    [ForIn Id ρ (α × β)] (m : ExtHashMapD α β) (l : ρ) := Id.run do
  let mut m := m
  for (a, b) in l do
    m := m.set a b
  return m

def ofList (l : List (α × β)) : ExtHashMapD α β := (∅ : ExtHashMapD α β).insertMany l

def modify (m : ExtHashMapD α β) (a : α) (f : β → β) : ExtHashMapD α β :=
  ⟨m.inner.alter a (fun | none => none | some b => let b' := f b; if b' == default then none else some b'),
    by sorry⟩

def alter (m : ExtHashMapD α β) (a : α) (f : Option β → Option β) : ExtHashMapD α β :=
  ⟨m.inner.alter a (fun b? => let b?' := f b?; if b?' == some default then none else b?'), by sorry⟩

end ExtHashMapD
