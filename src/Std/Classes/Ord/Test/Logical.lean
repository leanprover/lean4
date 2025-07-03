module

prelude
import Init.Core
import Init.Data.Ord
import Init.Data.List.Lex

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
  le := fun a b => ¬ lt b a
  lt := fun a b => le a b ∧ ¬ le b a

class LEDefinedPreorder (α : Type u) [Preorder α] where
  lt_iff_le_not_ge : ∀ a b : α, LT.lt a b ↔ LE.le a b ∧ ¬ LE.le b a := by intros; rfl

-- support function arguments?
class Antisymm (α : Type u) [LE α] where
  le_antisymm : ∀ a b : α, LE.le a b → LE.le b a → a = b

abbrev _root_.LE.Antisymm (α : Type u) (_ : LE α) := Test.Antisymm α

class Reflexive (α : Type u) [LE α] where
  refl : ∀ a : α, LE.le a a

abbrev _root_.LE.Reflexive (α : Type u) (_ : LE α) := Test.Reflexive α

class LawfulPreorder (α : Type u) [Preorder α] extends LEDefinedPreorder α, Reflexive α where
  le_trans : ∀ a b c : α, LE.le a b → LE.le b c → LE.le a c

class LogicalOrd (α : Type u) where
  logicalOrd : Logical (Ord α)

class OrientedOrd (α : Type u) extends LogicalOrd α, Preorder α where

noncomputable def LogicalOrd.compare {α : Type u} [LogicalOrd α] (a b : α) : Ordering :=
  LogicalOrd.logicalOrd.get.compare a b

class LawfulOrientedOrd (α : Type u) [OrientedOrd α] extends LEDefinedPreorder α where
  compare_eq_lt_iff_lt : ∀ a b : α, LogicalOrd.compare a b = .lt ↔ LT.lt a b
  compare_isLE_iff_le : ∀ a b : α, (LogicalOrd.compare a b).isLE ↔ LE.le a b
  compare_isGE_iff_ge : ∀ a b : α, (LogicalOrd.compare a b).isGE ↔ LE.le b a

abbrev OrientedOrd.Lawful {α : Type u} (ord : OrientedOrd α) := LawfulOrientedOrd α

-- do we want these empty marker classes?
class PartialOrder (α : Type u) extends Preorder α where

class LawfulPartialOrder (α : Type u) [PartialOrder α] extends LawfulPreorder α, Antisymm α where

class LinearPreorder (α : Type u) extends Preorder α, LogicalMin α, LogicalMax α, OrientedOrd α where

class LawfulLinearPreorder (α : Type u) [LinearPreorder α] extends LawfulPreorder α,
    LawfulOrientedOrd α where
  min_eq : ∀ a b : α, LogicalMin.min a b = open scoped Classical in if LE.le a b then a else b
  max_eq : ∀ a b : α, LogicalMax.max a b = open scoped Classical in if LE.le a b then b else a

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

def Preorder.ofBLE {α} [BLE α] : Preorder α where
  le a b := BLE.LE a b

def Preorder.ofLE {α} [LE α] : Preorder α where
  le a b := LE.le a b

def Preorder.ofBLT {α} [BLT α] : Preorder α where
  lt a b := BLT.LT a b

def Preorder.ofLT {α} [LT α] : Preorder α where
  lt a b := LT.lt a b

def LogicalOrd.ofBLE {α} [BLE α] : LogicalOrd α where
  logicalOrd := .ofComputable .ofBLE

def OrientedOrd.ofBLE {α} [BLE α] : OrientedOrd α where
  toPreorder := .ofBLE
  toLogicalOrd := .ofBLE

def LogicalOrd.ofLE {α} [LE α] : LogicalOrd α where
  logicalOrd := .ofComputable .ofLE

def OrientedOrd.ofLE {α} [LE α] : OrientedOrd α where
  toPreorder := .ofLE
  toLogicalOrd := .ofLE

def LogicalOrd.ofBLT {α} [BLT α] : LogicalOrd α where
  logicalOrd := .ofComputable .ofBLT

def OrientedOrd.ofBLT {α} [BLT α] : OrientedOrd α where
  toPreorder := .ofBLT
  toLogicalOrd := .ofBLT

def LogicalOrd.ofLT {α} [LT α] : LogicalOrd α where
  logicalOrd := .ofComputable .ofLT

def OrientedOrd.ofLT {α} [LT α] : OrientedOrd α where
  toPreorder := .ofLT
  toLogicalOrd := .ofLT

def OrientedOrd.ofLogicalOrd (ord : LogicalOrd α := by infer_instance) : OrientedOrd α :=
  { toLogicalOrd := ord
    lt a b := ord.compare a b = .lt
    le a b := (ord.compare a b).isLE }

class OrientedOrd.LawfulLT (α : Type u) [i : LT α] [OrientedOrd α] where
  lt_iff_lt {a b : α} : OrientedOrd.toPreorder.lt a b ↔ i.lt a b
  gt_iff_gt {a b : α} : OrientedOrd.toPreorder.lt b a ↔ i.lt b a

class OrientedOrd.LawfullyDeterminedByLT (α : Type u) [LT α] where
  lawful : OrientedOrd.ofLT.Lawful (α := α)
  lawful_lt : OrientedOrd.ofLT.LawfulLT α

abbrev LogicalOrd.LawfulLT (α : Type u) [i : LT α] [LogicalOrd α] :=
  (OrientedOrd.ofLogicalOrd inferInstance).LawfulLT α

class OrientedOrd.LawfulLE (α : Type u) [i : LE α] [OrientedOrd α] where
  le_iff_le {a b : α} : OrientedOrd.toPreorder.toLE.le a b ↔ i.le a b

class OrientedOrd.LawfulBLT (α : Type u) [i : BLT α] [OrientedOrd α] where
  lt_iff_lt {a b : α} : OrientedOrd.toPreorder.toLT.lt a b ↔ i.LT a b

class OrientedOrd.LawfulBLE (α : Type u) [i : BLE α] [OrientedOrd α] where
  le_iff_le {a b : α} : OrientedOrd.toPreorder.toLE.le a b ↔ i.LE a b

class Assign {α : Type u} (a : outParam α) (b : α) where
  eq : a = b

instance (α : Type u) (a : α) : Assign a a where
  eq := rfl

-- attribute [local instance] LogicalOrd.ofBLE in
-- example [BLE α] [BLT α] [LogicalOrd.ofBLE.LawfulBLE α] [LogicalOrd.ofBLE.LawfulBLT α] (a b : α)
--     (h : BLT.LT a b) : BLE.LE a b := by
--   simp only [← LogicalOrd.LawfulBLE.compare_isBLE_iff_le,
--     ← LogicalOrd.LawfulBLT.compare_eq_lt_iff_lt] at ⊢ h
--   simp [h]

-- theorem s [BLE α] [BLT α] {x : LogicalOrd α} [Assign x LogicalOrd.ofBLE] [LogicalOrd.LawfulBLE α] [LogicalOrd.LawfulBLT α] {a b : α}
--     (h : BLT.LT a b) : BLE.LE a b := by
--   simp only [← LogicalOrd.LawfulBLE.compare_isBLE_iff_le,
--     ← LogicalOrd.LawfulBLT.compare_eq_lt_iff_lt] at ⊢ h
--   simp [h]

-- example [BLE α] [BLT α] [LogicalOrd.ofBLE.LawfulBLE α] [LogicalOrd.ofBLE.LawfulBLT α]
--     (a b : α) (h : BLT.LT a b) : BLE.LE a b := s h

-- theorem t [BLE α] [BLT α] {x : LogicalOrd α} [LogicalOrd.LawfulBLE α] [LogicalOrd.LawfulBLT α] {a b : α}
--     (h : BLT.LT a b) (_x : x = LogicalOrd.ofBLE := by rfl) : BLE.LE a b := by
--   simp only [← LogicalOrd.LawfulBLE.compare_isBLE_iff_le,
--     ← LogicalOrd.LawfulBLT.compare_eq_lt_iff_lt] at ⊢ h
--   simp [h]

-- example [BLE α] [BLT α] [LogicalOrd.ofBLE.LawfulBLE α] [LogicalOrd.ofBLE.LawfulBLT α]
--     (a b : α) (h : BLT.LT a b) : BLE.LE a b := t h

section Demo

open _root_.List

theorem irrefl [i : LT α] [OrientedOrd.LawfullyDeterminedByLT α] [OrientedOrd.ofLT.Reflexive α]
    (a : α) : ¬ i.lt a a := by
  sorry

theorem asymm [i : LT α] [OrientedOrd.LawfullyDeterminedByLT α] (a b : α) : i.lt a b → ¬ i.lt b a := by
  sorry

theorem lt_antisymm [i : LT α] [OrientedOrd.LawfullyDeterminedByLT α] (a b : α) : ¬ i.lt a b → ¬ i.lt b a → a = b := by
  sorry

protected theorem List.le_iff_exists [LT α] [OrientedOrd.LawfullyDeterminedByLT α]
    [OrientedOrd.ofLT.Antisymm α] [OrientedOrd.ofLT.Reflexive α] {l₁ l₂ : List α} :
    l₁ ≤ l₂ ↔
      (l₁ = l₂.take l₁.length) ∨
        (∃ (i : Nat) (h₁ : i < l₁.length) (h₂ : i < l₂.length),
          (∀ j, (hj : j < i) →
            l₁[j]'(Nat.lt_trans hj h₁) = l₂[j]'(Nat.lt_trans hj h₂)) ∧ l₁[i] < l₂[i]) := by
  open Classical in
  rw [← lex_eq_false_iff_ge, lex_eq_false_iff_exists]
  · simp only [isEqv_eq, beq_iff_eq, decide_eq_true_eq]
    simp only [eq_comm]
    conv => lhs; simp +singlePass [exists_comm]
  · simpa using irrefl
  · simpa using asymm
  · simpa using lt_antisymm

protected theorem List.map_le
    [LT α] [OrientedOrd.LawfullyDeterminedByLT α]
    [OrientedOrd.ofLT.Antisymm α] [OrientedOrd.ofLT.Reflexive α]
    [LT β] [OrientedOrd.LawfullyDeterminedByLT β]
    [OrientedOrd.ofLT.Antisymm β] [OrientedOrd.ofLT.Reflexive β]
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

-- Note: Can we formulate these lemmas more abstractly without making them inconvenient?

end Demo

end Std.Classes.Test
