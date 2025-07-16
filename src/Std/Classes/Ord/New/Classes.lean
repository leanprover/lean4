module

prelude
public import Init.Core
import Init.SimpLemmas
import Init.Data.Subtype

public class OrderData (α : Type u) where
  IsLE : α → α → Prop

public class Preorder (α : Type u) [OrderData α] where
  le_refl : ∀ a : α, OrderData.IsLE a a
  le_trans : ∀ a b c : α, OrderData.IsLE a b → OrderData.IsLE b c → OrderData.IsLE a c

public class PartialOrder (α : Type u) [OrderData α] extends Preorder α where
  le_antisymm : ∀ a b : α, OrderData.IsLE a b → OrderData.IsLE b a → a = b

public class LinearPreorder (α : Type u) [OrderData α] extends Preorder α where
  le_total : ∀ a b : α, OrderData.IsLE a b ∨ OrderData.IsLE b a

public class LinearOrder (α : Type u) [OrderData α] extends PartialOrder α, LinearPreorder α

-- public structure OrderedSubtype {α : Type u} (P : α → Prop) where
--   val : α
--   property : P val

public instance {α : Type u} [LE α] {P : α → Prop} : LE (Subtype P) where
  le a b := a.val ≤ b.val

public instance {α : Type u} [OrderData α] {P : α → Prop} : OrderData (Subtype P) where
  IsLE a b := OrderData.IsLE a.val b.val

section LE

public class LawfulOrderLE (α : Type u) [LE α] [OrderData α] where
  le_iff : ∀ a b : α, a ≤ b ↔ OrderData.IsLE a b

public instance {α : Type u} [LE α] [OrderData α] [LawfulOrderLE α] [PartialOrder α] :
    Std.Antisymm (fun a b : α => a ≤ b) where
  antisymm a b := by
    simp only [LawfulOrderLE.le_iff]
    apply PartialOrder.le_antisymm

public instance {α : Type u} [LE α] [OrderData α] [LawfulOrderLE α] [Preorder α] :
    Trans (α := α) (· ≤ ·) (· ≤ ·) (· ≤ ·) where
  trans := by simpa [LawfulOrderLE.le_iff] using fun {a b c} => Preorder.le_trans (α := α) a b c

public theorem le_refl {α : Type u} [LE α] [OrderData α] [LawfulOrderLE α] [Preorder α] (a : α) :
    a ≤ a := by
  simp [LawfulOrderLE.le_iff, Preorder.le_refl]

public theorem le_antisymm {α : Type u} [LE α] [Std.Antisymm (α := α) (· ≤ ·)] {a b : α}
    (hab : a ≤ b) (hba : b ≤ a) : a = b :=
  Std.Antisymm.antisymm _ _ hab hba

public theorem le_trans {α : Type u} [LE α] [Trans (α := α) (· ≤ ·) (· ≤ ·) (· ≤ ·)] {a b c : α}
    (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c :=
  Trans.trans hab hbc

public noncomputable scoped instance Classical.Order.instLE {α : Type u} [OrderData α] :
    LE α where
  le a b := OrderData.IsLE a b

open Classical.Order in
public instance {α : Type u} [OrderData α] :
    LawfulOrderLE α where
  le_iff _ _ := Iff.rfl

end LE

section Min

public class MinEqOr (α : Type u) [Min α] where
  min_eq_or : ∀ a b : α, min a b = a ∨ min a b = b

public def MinEqOr.elim {α : Type u} [Min α] [MinEqOr α] {P : α → Prop} {a b : α} (ha : P a) (hb : P b) :
    P (min a b) := by
  cases MinEqOr.min_eq_or a b <;> simp_all

public theorem min_self {α : Type u} [Min α] [Std.IdempotentOp (min : α → α → α)] {a : α} :
    min a a = a :=
  Std.IdempotentOp.idempotent a

public class LawfulOrderInf (α : Type u) [Min α] [OrderData α] where
  le_min_iff : ∀ a b c : α, OrderData.IsLE a (min b c) ↔ OrderData.IsLE a b ∧ OrderData.IsLE a c

public theorem le_min_iff {α : Type u} [Min α] [LE α] [OrderData α]
    [LawfulOrderLE α] [LawfulOrderInf α] {a b c : α} :
    a ≤ min b c ↔ a ≤ b ∧ a ≤ c := by
  simpa [LawfulOrderLE.le_iff] using LawfulOrderInf.le_min_iff a b c

public theorem min_le_left {α : Type u} [Min α] [LE α] [OrderData α] [Preorder α]
    [LawfulOrderLE α] [LawfulOrderInf α] {a b : α} :
    min a b ≤ a :=
  le_min_iff.mp (le_refl _) |>.1

public theorem min_le_right {α : Type u} [Min α] [LE α] [OrderData α] [Preorder α]
    [LawfulOrderLE α] [LawfulOrderInf α] {a b : α} :
    min a b ≤ b :=
  le_min_iff.mp (le_refl _) |>.2

public class LawfulOrderMin (α : Type u) [Min α] [OrderData α] extends MinEqOr α, LawfulOrderInf α

public theorem min_le {α : Type u} [Min α] [LE α] [OrderData α] [Preorder α]
    [LawfulOrderLE α] [LawfulOrderMin α] {a b c : α} :
    min a b ≤ c ↔ a ≤ c ∨ b ≤ c := by
  cases MinEqOr.min_eq_or a b <;> rename_i h
  · simpa [h] using le_trans (h ▸ min_le_right (a := a) (b := b))
  · simpa [h] using le_trans (h ▸ min_le_left (a := a) (b := b))

public instance {α : Type u} [Min α] [MinEqOr α] {P : α → Prop} : Min (Subtype P) where
  min a b := ⟨Min.min a.val b.val, MinEqOr.elim a.property b.property⟩

public instance {α : Type u} [LE α] {P : α → Prop} : LE (Subtype P) where
  le a b := a.val ≤ b.val

public instance {α : Type u} [Min α] [MinEqOr α] :
    Std.IdempotentOp (min : α → α → α) where
  idempotent a := by cases MinEqOr.min_eq_or a a <;> assumption

open Classical.Order in
public instance {α : Type u} [OrderData α] [Min α] [LinearOrder α] [LawfulOrderMin α] :
    Std.Associative (min : α → α → α) where
  assoc a b c := by apply le_antisymm <;> simp [min_le, le_min_iff, le_refl]

public instance {α : Type u} [LE α] [OrderData α] [LawfulOrderLE α]
    {P : α → Prop} : LawfulOrderLE (Subtype P) where
  le_iff a b := by simp [LE.le, OrderData.IsLE, LawfulOrderLE.le_iff]

public theorem min_eq_or {α : Type u} [Min α] [MinEqOr α] {a b : α} :
    min a b = a ∨ min a b = b :=
  MinEqOr.min_eq_or a b

end Min

section Max

public class MaxEqOr (α : Type u) [Max α] where
  max_eq_or : ∀ a b : α, max a b = a ∨ max a b = b

public def MaxEqOr.elim {α : Type u} [Max α] [MaxEqOr α] {P : α → Prop} {a b : α} (ha : P a) (hb : P b) :
    P (max a b) := by
  cases MaxEqOr.max_eq_or a b <;> simp_all

public theorem max_self {α : Type u} [Max α] [Std.IdempotentOp (max : α → α → α)] {a : α} :
    max a a = a :=
  Std.IdempotentOp.idempotent a

public class LawfulOrderSup (α : Type u) [Max α] [OrderData α] where
  max_le_iff : ∀ a b c : α, OrderData.IsLE (max a b) c ↔ OrderData.IsLE a c ∧ OrderData.IsLE b c

public theorem max_le_iff {α : Type u} [Max α] [LE α] [OrderData α]
    [LawfulOrderLE α] [LawfulOrderSup α] {a b c : α} :
    max a b ≤ c ↔ a ≤ c ∧ b ≤ c := by
  simpa [LawfulOrderLE.le_iff] using LawfulOrderSup.max_le_iff a b c

public theorem left_le_max {α : Type u} [Max α] [LE α] [OrderData α] [Preorder α]
    [LawfulOrderLE α] [LawfulOrderSup α] {a b : α} :
    a ≤ max a b :=
  max_le_iff.mp (le_refl _) |>.1

public theorem right_le_max {α : Type u} [Max α] [LE α] [OrderData α] [Preorder α]
    [LawfulOrderLE α] [LawfulOrderSup α] {a b : α} :
    b ≤ max a b :=
  max_le_iff.mp (le_refl _) |>.2

public class LawfulOrderMax (α : Type u) [Max α] [OrderData α] extends MaxEqOr α, LawfulOrderSup α

public theorem le_max {α : Type u} [Max α] [LE α] [OrderData α] [Preorder α]
    [LawfulOrderLE α] [LawfulOrderMax α] {a b c : α} :
    a ≤ max b c ↔ a ≤ b ∨ a ≤ c := by
  cases MaxEqOr.max_eq_or b c <;> rename_i h
  · simpa [h] using (le_trans · (h ▸ right_le_max))
  · simpa [h] using (le_trans · (h ▸ left_le_max))

public instance {α : Type u} [Max α] [MaxEqOr α] {P : α → Prop} : Max (Subtype P) where
  max a b := ⟨Max.max a.val b.val, MaxEqOr.elim a.property b.property⟩

public instance {α : Type u} [Max α] [MaxEqOr α] :
    Std.IdempotentOp (max : α → α → α) where
  idempotent a := by cases MaxEqOr.max_eq_or a a <;> assumption

open Classical.Order in
public instance {α : Type u} [OrderData α] [Max α] [LinearOrder α] [LawfulOrderMax α] :
    Std.Associative (max : α → α → α) where
  assoc a b c := by
    apply le_antisymm
    all_goals
      simp only [max_le_iff]
      simp [le_max, le_refl]

public theorem max_eq_or {α : Type u} [Max α] [MaxEqOr α] {a b : α} :
    max a b = a ∨ max a b = b :=
  MaxEqOr.max_eq_or a b

end Max
