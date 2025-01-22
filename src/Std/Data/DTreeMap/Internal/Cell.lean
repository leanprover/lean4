import Orderedtree.Classes.TransOrd
import Orderedtree.Classes.LawfulEqOrd

/-!
# The `Cell` type
-/

set_option autoImplicit false
set_option linter.all true

universe u v w

variable {α : Type u} {β : α → Type v} {γ : α → Type w} {δ : Type w}

namespace Std.DTreeMap.Internal

/-- Type for representing the place in a tree map where a mapping for `k` could live. -/
structure Cell (α : Type u) [Ord α] (β : α → Type v) (k : α → Ordering) where
  /-- The mapping. -/
  inner : Option ((a : α) × β a)
  /-- If there is a mapping, then it has a matching key. -/
  property : ∀ [OrientedOrd α], ∀ p, inner = some p → k p.1 = .eq

namespace Cell

/-- Create a cell with a matching key. -/
def ofEq [Ord α] {k : α → Ordering} (k' : α) (v' : β k') (hcmp : ∀ [OrientedOrd α], k k' = .eq) :
    Cell α β k :=
  ⟨some ⟨k', v'⟩, by intro _ p hp; obtain rfl := Option.some_inj.1 hp; simpa using hcmp⟩

/-- Create a cell with a matching key. -/
def of [Ord α] (k : α) (v : β k) : Cell α β (compare k) :=
  .ofEq k v (by intro; simp)

@[simp] theorem ofEq_inner [Ord α] {k : α → Ordering} {k' : α} {v' : β k'} {h} :
  (Cell.ofEq k' v' h : Cell α β k).inner = some ⟨k', v'⟩ := rfl
@[simp] theorem of_inner [Ord α] {k : α} {v : β k} : (Cell.of k v).inner = some ⟨k, v⟩ := rfl

/-- Create an empty cell. -/
def empty [Ord α] {k : α → Ordering} : Cell α β k :=
  ⟨none, by simp⟩

@[simp] theorem empty_inner [Ord α] {k : α → Ordering} : (Cell.empty : Cell α β k).inner = none := rfl

def contains [Ord α] {k : α → Ordering} (c : Cell α β k) : Bool :=
  c.inner.isSome

@[simp] theorem contains_of [Ord α] {k : α} {v : β k} : (Cell.of k v).contains = true := rfl
@[simp] theorem contains_ofEq [Ord α] {k : α → Ordering} {k' : α} {v' : β k'} {h} :
    (Cell.ofEq k' v' h : Cell α β k).contains = true := rfl
@[simp] theorem contains_empty [Ord α] {k : α → Ordering} : (Cell.empty : Cell α β k).contains = false := rfl

def get? [Ord α] [OrientedOrd α] [LawfulEqOrd α] {k : α} (c : Cell α β (compare k)) : Option (β k) :=
  match h : c.inner with
  | none => none
  | some p => some (cast (congrArg β (eq_of_compare (c.property _ h)).symm) p.2)

@[simp]
theorem get?_empty [Ord α] [OrientedOrd α] [LawfulEqOrd α] {k : α} :
    (Cell.empty : Cell α β (compare k)).get? = none :=
  rfl

def get [Ord α] [OrientedOrd α] [LawfulEqOrd α] {k : α} (c : Cell α β (compare k)) (h : c.contains) : β k :=
  match hc : c.inner with
  | none => False.elim (by simp [contains, hc] at h)
  | some p => (cast (congrArg β (eq_of_compare (c.property _ hc)).symm) p.2)

theorem ext [Ord α] {k : α → Ordering} {c c' : Cell α β k} : c.inner = c'.inner → c = c' := by
  cases c; cases c'; simp

end Cell

def List.findCell [Ord α] (l : List ((a : α) × β a)) (k : α → Ordering) : Cell α β k where
  inner := l.find? (k ·.1 == .eq)
  property p hp := by simpa using (List.find?_eq_some_iff_append.1 hp).1

theorem List.findCell_inner [Ord α] (l : List ((a : α) × β a)) (k : α → Ordering) :
    (findCell l k).inner = l.find? (k ·.1 == .eq) := rfl

@[simp] theorem List.findCell_nil [Ord α] (k : α → Ordering) : (findCell [] k : Cell α β k) = .empty := rfl

end Std.DTreeMap.Internal
