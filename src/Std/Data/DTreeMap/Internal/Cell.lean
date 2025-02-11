/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Std.Classes.Ord
import Std.Data.Internal.List.Associative

/-!
# The `Cell` type
-/

set_option autoImplicit false
set_option linter.all true

universe u v w

variable {α : Type u} {β : α → Type v} {γ : α → Type w} {δ : Type w}

namespace Std.DTreeMap.Internal
open Std.Internal.List
open Std.Internal (beqOfOrd beq_eq)

attribute [local instance] beqOfOrd

/--
Type for representing the place in a tree map where a mapping for `k` could live.
Internal implementation detail of the tree map.
-/
structure Cell (α : Type u) [Ord α] (β : α → Type v) (k : α → Ordering) where
  /-- The mapping. -/
  inner : Option ((a : α) × β a)
  /-- If there is a mapping, then it has a matching key. -/
  property : ∀ [OrientedOrd α], ∀ p, inner = some p → k p.1 = .eq

namespace Cell

/-- Create a cell with a matching key. Internal implementation detail of the tree map -/
def ofEq [Ord α] {k : α → Ordering} (k' : α) (v' : β k') (hcmp : ∀ [OrientedOrd α], k k' = .eq) :
    Cell α β k :=
  ⟨some ⟨k', v'⟩, by intro _ p hp; obtain rfl := Option.some_inj.1 hp; simpa using hcmp⟩

/-- Create a cell with a matching key. Internal implementation detail of the tree map -/
def of [Ord α] (k : α) (v : β k) : Cell α β (compare k) :=
  .ofEq k v (by intro; simp)

@[simp]
theorem ofEq_inner [Ord α] {k : α → Ordering} {k' : α} {v' : β k'} {h} :
  (Cell.ofEq k' v' h : Cell α β k).inner = some ⟨k', v'⟩ := rfl

@[simp]
theorem of_inner [Ord α] {k : α} {v : β k} : (Cell.of k v).inner = some ⟨k, v⟩ := rfl

/-- Create an empty cell. Internal implementation detail of the tree map -/
def empty [Ord α] {k : α → Ordering} : Cell α β k :=
  ⟨none, by simp⟩

/-- Internal implementation detail of the tree map -/
def ofOption [Ord α] (k : α) (v? : Option (β k)) : Cell α β (compare k) :=
  match v? with
  | none => .empty
  | some v => .of k v

@[simp]
theorem empty_inner [Ord α] {k : α → Ordering} : (Cell.empty : Cell α β k).inner = none := rfl

/-- Internal implementation detail of the tree map -/
def contains [Ord α] {k : α → Ordering} (c : Cell α β k) : Bool :=
  c.inner.isSome

@[simp]
theorem contains_of [Ord α] {k : α} {v : β k} : (Cell.of k v).contains = true := rfl

@[simp]
theorem contains_ofEq [Ord α] {k : α → Ordering} {k' : α} {v' : β k'} {h} :
    (Cell.ofEq k' v' h : Cell α β k).contains = true := rfl

@[simp]
theorem contains_empty [Ord α] {k : α → Ordering} : (Cell.empty : Cell α β k).contains = false := rfl

theorem containsKey_inner_toList [Ord α] [OrientedOrd α] {k : α} {c : Cell α β (compare k)} :
    c.contains → containsKey k c.inner.toList := by
  obtain ⟨(_|p), hp⟩ := c
  · simp [Cell.contains]
  · simp only [Cell.contains, Option.isSome_some, Option.toList_some, forall_const]
    exact containsKey_cons_of_beq (by simpa [beq_eq] using (OrientedCmp.eq_symm (hp p rfl)))

/-- Internal implementation detail of the tree map -/
def get? [Ord α] [OrientedOrd α] [LawfulEqOrd α] {k : α} (c : Cell α β (compare k)) : Option (β k) :=
  match h : c.inner with
  | none => none
  | some p => some (cast (congrArg β (compare_eq_iff_eq.mp (c.property _ h)).symm) p.2)

@[simp]
theorem get?_empty [Ord α] [OrientedOrd α] [LawfulEqOrd α] {k : α} :
    (Cell.empty : Cell α β (compare k)).get? = none :=
  rfl

/-- Internal implementation detail of the tree map -/
def alter [Ord α] [OrientedOrd α] [LawfulEqOrd α] {k : α}
    (f : Option (β k) → Option (β k)) (c : Cell α β (compare k)) :
    Cell α β (compare k) :=
  match h : c.inner with
  | none => .ofOption k <| f none
  | some ⟨k', v'⟩ =>
    have heq : β k' = β k := congrArg β <| compare_eq_iff_eq.mp (c.property _ h) |>.symm
    .ofOption k <| f <| some <| cast heq v'

theorem ext [Ord α] {k : α → Ordering} {c c' : Cell α β k} : c.inner = c'.inner → c = c' := by
  cases c; cases c'; simp

namespace Const

variable {β : Type v}

/-- Internal implementation detail of the tree map -/
def get? [Ord α] {k : α} (c : Cell α (fun _ => β) (compare k)) : Option β :=
  match c.inner with
  | none => none
  | some p => some p.2

@[simp]
theorem get?_empty [Ord α] {k : α} :
    get? (Cell.empty : Cell α (fun _ => β) (compare k)) = none :=
  rfl

/-- Internal implementation detail of the tree map -/
def alter [Ord α] [OrientedOrd α] {k : α}
    (f : Option β → Option β) (c : Cell α (fun _ => β) (compare k)) :
    Cell α (fun _ => β) (compare k) :=
  match c.inner with
  | none => .ofOption k <| f none
  | some ⟨_, v'⟩ =>
    .ofOption k <| f <| some v'

end Const

end Cell

/-- Internal implementation detail of the tree map -/
def List.findCell [Ord α] (l : List ((a : α) × β a)) (k : α → Ordering) : Cell α β k where
  inner := l.find? (k ·.1 == .eq)
  property p hp := by simpa using (List.find?_eq_some_iff_append.1 hp).1

theorem List.findCell_inner [Ord α] (l : List ((a : α) × β a)) (k : α → Ordering) :
    (findCell l k).inner = l.find? (k ·.1 == .eq) := rfl

@[simp]
theorem List.findCell_nil [Ord α] (k : α → Ordering) : (findCell [] k : Cell α β k) = .empty := rfl

end Std.DTreeMap.Internal
