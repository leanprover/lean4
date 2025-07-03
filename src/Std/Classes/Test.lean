prelude
import Init.Core
import Init.Data.Ord
import Lean

namespace Std.Classes.Test

class BLE (α : Type u) where
  LE : α → α → Bool

class LE (α : Type u) where
  LE : α → α → Prop

class LawfulBLE (α : Type u) [LE α] [BLE α] where
  ble_iff_le : ∀ a b : α, BLE.LE a b ↔ LE.LE a b

abbrev DecidableLE (α : Type u) [LE α] :=
  DecidableRel (fun a b : α => LE.LE a b)

instance (α : Type u) [BLE α] [LE α] [LawfulBLE α] : DecidableLE α :=
  fun a b => if h : BLE.LE a b then
      .isTrue (LawfulBLE.ble_iff_le _ _ |>.mp h)
    else
      .isFalse (h.imp (LawfulBLE.ble_iff_le _ _).mpr)

class BLT (α : Type u) where
  LT : α → α → Bool

class LT (α : Type u) where
  LT : α → α → Prop

class LawfulBLT (α : Type u) [LT α] [BLT α] where
  blt_iff_lt : ∀ a b : α, BLT.LT a b ↔ LT.LT a b

abbrev DecidableLT (α : Type u) [LT α] := DecidableRel (fun a b : α => LT.LT a b)

instance (α : Type u) [BLT α] [LT α] [LawfulBLT α] : DecidableLT α :=
  fun a b => if h : BLT.LT a b then
      .isTrue (LawfulBLT.blt_iff_lt _ _ |>.mp h)
    else
      .isFalse (h.imp (LawfulBLT.blt_iff_lt _ _).mpr)

class Ord (α : Type u) where
  compare : α → α → Ordering

class Noncomputable (α : Type u) where
  Predicate : α → Prop
  nonempty : Nonempty (Subtype Predicate)
  subsingleton : Subsingleton (Subtype Predicate)

def Noncomputable.ofComputable {α : Type u} (a : α) : Noncomputable α where
  Predicate := (· = a)
  nonempty := ⟨⟨a, rfl⟩⟩
  subsingleton := .intro fun a b => Subtype.ext (a.2.trans b.2.symm)

noncomputable def Noncomputable.get (i : Noncomputable α := by infer_instance) :=
  haveI := i.nonempty
  (Classical.ofNonempty (α := Subtype i.Predicate)).val

abbrev LogicalOrd (α : Type u) := Noncomputable (Ord α)

noncomputable def LogicalOrd.instOrd {α : Type u} [i : LogicalOrd α] : Ord α :=
  Noncomputable.get

noncomputable def LogicalOrd.compare {α : Type u} [LogicalOrd α] (a b : α) : Ordering :=
  LogicalOrd.instOrd.compare a b

class OrdForOrd (α : Type u) [LogicalOrd α] [i : Ord α] where
  eq : LogicalOrd.instOrd = i

class LogicalOrd.LawfulLT (α : Type u) [LT α] [LogicalOrd α] where
  compare_eq_lt_iff_lt {a b : α} : LogicalOrd.compare a b = .lt ↔ LT.LT a b
  compare_eq_gt_iff_gt {a b : α} : LogicalOrd.compare a b = .gt ↔ LT.LT b a

class LogicalOrd.LawfulLE (α : Type u) [LE α] [LogicalOrd α] where
  compare_isLE_iff_le {a b : α} : (LogicalOrd.compare a b).isLE ↔ LE.LE a b
  compare_eq_ge_iff_ge {a b : α} : (LogicalOrd.compare a b).isLE ↔ LE.LE b a

class LogicalOrd.LawfulBLT (α : Type u) [BLT α] [LogicalOrd α] where
  compare_eq_lt_iff_lt {a b : α} : LogicalOrd.compare a b = .lt ↔ BLT.LT a b
  compare_eq_gt_iff_gt {a b : α} : LogicalOrd.compare a b = .gt ↔ BLT.LT b a

class LogicalOrd.LawfulBLE (α : Type u) [BLE α] [LogicalOrd α] where
  compare_isBLE_iff_le {a b : α} : (LogicalOrd.compare a b).isLE ↔ BLE.LE a b
  compare_eq_ge_iff_ge {a b : α} : (LogicalOrd.compare a b).isLE ↔ BLE.LE b a

class Min (α : Type u) where
  min : α → α → α

abbrev LogicalMin (α : Type u) := Noncomputable (Min α)

class Max (α : Type u) where
  max : α → α → α

abbrev LogicalMax (α : Type u) := Noncomputable (Max α)

class LogicalMin.LawfulMin (α : Type u) [LogicalMin α] [i : Min α] where
  eq : Noncomputable.get = i

class LogicalMax.LawfulMax (α : Type u) [LogicalMax α] [i : Max α] where
  eq : Noncomputable.get = i

def Ord.ofBLE {α} [BLE α] : Ord α where
  compare a b := if BLE.LE a b then
      if BLE.LE b a then .eq else .lt
    else
      .gt

noncomputable def BLE.ofLE {α} [i : Std.Classes.Test.LE α] : BLE α where
  LE a b := open scoped Classical in decide (i.LE a b)

def LogicalOrd.ofBLE {α} [BLE α] : LogicalOrd α := .ofComputable .ofBLE

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

end Std.Classes.Test
