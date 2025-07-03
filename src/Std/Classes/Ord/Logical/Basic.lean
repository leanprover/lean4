module

prelude
import Init.Core
import Init.Data.Ord

namespace Std.Classes.Test

section General

class Logical (α : Type u) where
  Predicate : α → Prop
  nonempty : Nonempty (Subtype Predicate)
  subsingleton : Subsingleton (Subtype Predicate)

def Logical.ofComputable {α : Type u} (a : α) : Logical α where
  Predicate := (· = a)
  nonempty := ⟨⟨a, rfl⟩⟩
  subsingleton := .intro fun a b => Subtype.ext (a.2.trans b.2.symm)

noncomputable def Logical.get (i : Logical α := by infer_instance) :=
  haveI := i.nonempty
  (Classical.ofNonempty (α := Subtype i.Predicate)).val

end General

section Classes

class BLE (α : Type u) where
  LE : α → α → Bool

-- class LE (α : Type u) where
--   LE : α → α → Prop

class LawfulBLE (α : Type u) [LE α] [BLE α] where
  ble_iff_le : ∀ a b : α, BLE.LE a b ↔ LE.le a b

abbrev DecidableLE (α : Type u) [LE α] :=
  DecidableRel (fun a b : α => LE.le a b)

instance (α : Type u) [BLE α] [LE α] [LawfulBLE α] : DecidableLE α :=
  fun a b => if h : BLE.LE a b then
      .isTrue (LawfulBLE.ble_iff_le _ _ |>.mp h)
    else
      .isFalse (h.imp (LawfulBLE.ble_iff_le _ _).mpr)

class BLT (α : Type u) where
  LT : α → α → Bool

-- class LT (α : Type u) where
--   LT : α → α → Prop

class LawfulBLT (α : Type u) [LT α] [BLT α] where
  blt_iff_lt : ∀ a b : α, BLT.LT a b ↔ LT.lt a b

abbrev DecidableLT (α : Type u) [LT α] := DecidableRel (fun a b : α => LT.lt a b)

instance (α : Type u) [BLT α] [LT α] [LawfulBLT α] : DecidableLT α :=
  fun a b => if h : BLT.LT a b then
      .isTrue (LawfulBLT.blt_iff_lt _ _ |>.mp h)
    else
      .isFalse (h.imp (LawfulBLT.blt_iff_lt _ _).mpr)

class Ord (α : Type u) where
  compare : α → α → Ordering

-- class LogicalOrd (α : Type u) where
--   logicalOrd : Logical (Ord α)

-- instance [LogicalOrd α] : Logical (Ord α) :=
--   LogicalOrd.logicalOrd

-- noncomputable def LogicalOrd.instOrd {α : Type u} [i : LogicalOrd α] : Ord α :=
--   Logical.get

-- noncomputable def LogicalOrd.compare {α : Type u} [LogicalOrd α] (a b : α) : Ordering :=
--   LogicalOrd.instOrd.compare a b

-- class OrdForOrd (α : Type u) [LogicalOrd α] [i : Ord α] where
--   eq : LogicalOrd.instOrd = i

-- class LogicalOrd.LawfulLT (α : Type u) [LT α] [LogicalOrd α] where
--   compare_eq_lt_iff_lt {a b : α} : LogicalOrd.compare a b = .lt ↔ LT.lt a b
--   compare_eq_gt_iff_gt {a b : α} : LogicalOrd.compare a b = .gt ↔ LT.lt b a

-- class LogicalOrd.LawfulLE (α : Type u) [LE α] [LogicalOrd α] where
--   compare_isLE_iff_le {a b : α} : (LogicalOrd.compare a b).isLE ↔ LE.le a b
--   compare_eq_ge_iff_ge {a b : α} : (LogicalOrd.compare a b).isLE ↔ LE.le b a

-- class LogicalOrd.LawfulBLT (α : Type u) [BLT α] [LogicalOrd α] where
--   compare_eq_lt_iff_lt {a b : α} : LogicalOrd.compare a b = .lt ↔ BLT.LT a b
--   compare_eq_gt_iff_gt {a b : α} : LogicalOrd.compare a b = .gt ↔ BLT.LT b a

-- class LogicalOrd.LawfulBLE (α : Type u) [BLE α] [LogicalOrd α] where
--   compare_isBLE_iff_le {a b : α} : (LogicalOrd.compare a b).isLE ↔ BLE.LE a b
--   compare_eq_ge_iff_ge {a b : α} : (LogicalOrd.compare a b).isLE ↔ BLE.LE b a

class Min (α : Type u) where
  min : α → α → α

class LogicalMin (α : Type u) where
  logicalMin : Logical (Min α)

instance [LogicalMin α] : Logical (Min α) :=
  LogicalMin.logicalMin

noncomputable def LogicalMin.min [LogicalMin α] (a b : α) : α :=
  (Logical.get : Min α).min a b

class Max (α : Type u) where
  max : α → α → α

class LogicalMax (α : Type u) where
  logicalMax : Logical (Max α)

instance [LogicalMax α] : Logical (Max α) :=
  LogicalMax.logicalMax

class LogicalMin.LawfulMin (α : Type u) [LogicalMin α] [i : Min α] where
  eq : Logical.get = i

noncomputable def LogicalMax.max [LogicalMax α] (a b : α) : α :=
  (Logical.get : Max α).max a b

class LogicalMax.LawfulMax (α : Type u) [LogicalMax α] [i : Max α] where
  eq : Logical.get = i

-- compare mathlib
class Preorder (α : Type u) extends LE α, LT α where
  le := fun a b => ¬ le b a
  lt := fun a b => le a b ∧ ¬ le b a

class LEDefinedPreorder (α : Type u) extends LE α, LT α where
  lt_iff_le_not_ge : ∀ a b : α, LT.lt a b ↔ LE.le a b ∧ ¬ LE.le b a := by intros; rfl

-- support function arguments?
class Antisymm (α : Type u) [LE α] where
  le_antisymm : ∀ a b : α, LE.le a b → LE.le b a → a = b

class LawfulPreorder (α : Type u) [Preorder α] extends LEDefinedPreorder α where
  le_refl : ∀ a : α, LE.le a a
  le_trans : ∀ a b c : α, LE.le a b → LE.le b c → LE.le a c

class LogicalOrd (α : Type u) extends Preorder α where

class LawfulLogicalOrd (α : Type u) [LogicalOrd α] extends LEDefinedPreorder α where

-- do we want these empty marker classes?
class PartialOrder (α : Type u) extends Preorder α where

class LawfulPartialOrder (α : Type u) [PartialOrder α] extends LawfulPreorder α, Antisymm α where

class LinearPreorder (α : Type u) extends Preorder α, LogicalMin α, LogicalMax α, LogicalOrd α where

class LawfulLinearPreorder (α : Type u) [LinearPreorder α] extends LawfulPreorder α where
  le_total (a b : α) : LE.le a b ∨ LE.le b a
  min_eq : ∀ a b : α, LogicalMin.min a b = open scoped Classical in if LE.le a b then a else b
  max_eq : ∀ a b : α, LogicalMax.max a b = open scoped Classical in if LE.le a b then b else a
  compare_eq : ∀ a b : α, LogicalOrd.compare a b =
    open scoped Classical in
    if LT.lt a b then .lt else if LT.lt b a then .gt else .eq

class LinearOrder (α : Type u) extends LinearPreorder α, PartialOrder α where

class LawfulLinearOrder (α : Type u) [LinearOrder α] extends LawfulLinearPreorder α,
    LawfulPartialOrder α where

end Classes

def Ord.ofBLE {α} [BLE α] : Ord α where
  compare a b := if BLE.LE a b then if BLE.LE b a then .eq else .lt else .gt

def Ord.ofBLT {α} [BLT α] : Ord α where
  compare a b := if BLT.LT a b then .lt else if BLT.LT b a then .gt else .eq

noncomputable def BLE.ofLE {α} [i : _root_.LE α] : BLE α where
  LE a b := open scoped Classical in decide (i.le a b)

noncomputable def Ord.ofLE {α} [i : _root_.LE α] : Ord α :=
  haveI : BLE α := .ofLE; .ofBLE

noncomputable def BLT.ofLT {α} [i : _root_.LT α] : BLT α where
  LT a b := open scoped Classical in decide (i.lt a b)

noncomputable def Ord.ofLT {α} [i : _root_.LT α] : Ord α :=
  haveI : BLT α := .ofLT; .ofBLT

def LogicalOrd.ofBLE {α} [BLE α] : LogicalOrd α := ⟨.ofComputable .ofBLE⟩

def LogicalOrd.ofLE {α} [LE α] : LogicalOrd α := ⟨.ofComputable .ofLE⟩

def LogicalOrd.ofBLT {α} [BLT α] : LogicalOrd α := ⟨.ofComputable .ofBLT⟩

def LogicalOrd.ofLT {α} [LT α] : LogicalOrd α := ⟨.ofComputable .ofLT⟩

class Assign {α : Type u} (a : outParam α) (b : α) where
  eq : a = b

instance (α : Type u) (a : α) : Assign a a where
  eq := rfl

attribute [local instance] LogicalOrd.ofBLE in
example [BLE α] [BLT α] [LogicalOrd.ofBLE.LawfulBLE α] [LogicalOrd.ofBLE.LawfulBLT α] (a b : α)
    (h : BLT.LT a b) : BLE.LE a b := by
  simp only [← LogicalOrd.LawfulBLE.compare_isBLE_iff_le,
    ← LogicalOrd.LawfulBLT.compare_eq_lt_iff_lt] at ⊢ h
  simp [h]

theorem s [BLE α] [BLT α] {x : LogicalOrd α} [Assign x LogicalOrd.ofBLE] [LogicalOrd.LawfulBLE α] [LogicalOrd.LawfulBLT α] {a b : α}
    (h : BLT.LT a b) : BLE.LE a b := by
  simp only [← LogicalOrd.LawfulBLE.compare_isBLE_iff_le,
    ← LogicalOrd.LawfulBLT.compare_eq_lt_iff_lt] at ⊢ h
  simp [h]

example [BLE α] [BLT α] [LogicalOrd.ofBLE.LawfulBLE α] [LogicalOrd.ofBLE.LawfulBLT α]
    (a b : α) (h : BLT.LT a b) : BLE.LE a b := s h

theorem t [BLE α] [BLT α] {x : LogicalOrd α} [LogicalOrd.LawfulBLE α] [LogicalOrd.LawfulBLT α] {a b : α}
    (h : BLT.LT a b) (_x : x = LogicalOrd.ofBLE := by rfl) : BLE.LE a b := by
  simp only [← LogicalOrd.LawfulBLE.compare_isBLE_iff_le,
    ← LogicalOrd.LawfulBLT.compare_eq_lt_iff_lt] at ⊢ h
  simp [h]

example [BLE α] [BLT α] [LogicalOrd.ofBLE.LawfulBLE α] [LogicalOrd.ofBLE.LawfulBLT α]
    (a b : α) (h : BLT.LT a b) : BLE.LE a b := t h

section Demo

protected theorem map_le [LT α] [LogicalOrd.ofLT.LawfulLT α]
    [LT β] [LogicalOrd.ofLT.LawfulLT α]
    [Std.Irrefl (· < · : α → α → Prop)]
    [Std.Asymm (· < · : α → α → Prop)]
    [Std.Antisymm (¬ · < · : α → α → Prop)]
    [Std.Irrefl (· < · : β → β → Prop)]
    [Std.Asymm (· < · : β → β → Prop)]
    [Std.Antisymm (¬ · < · : β → β → Prop)]
    {l₁ l₂ : List α} {f : α → β} (w : ∀ x y, x < y → f x < f y) (h : l₁ ≤ l₂) :
    map f l₁ ≤ map f l₂ := by
  rw [List.le_iff_exists] at h ⊢
  obtain (h | ⟨i, h₁, h₂, w₁, w₂⟩) := h
  · left
    rw [h]
    simp
  · right
    refine ⟨i, by simpa using h₁, by simpa using h₂, ?_, ?_⟩
    · simp +contextual [w₁]
    · simpa using w _ _ w₂

end Demo

end Std.Classes.Test
