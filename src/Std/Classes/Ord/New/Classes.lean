module

prelude
public import Init.Core
import Init.SimpLemmas

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

public structure OrderedSubtype {α : Type u} (P : α → Prop) where
  val : α
  property : P val

public instance {α : Type u} [LE α] {P : α → Prop} : LE (OrderedSubtype P) where
  le a b := a.val ≤ b.val

public instance {α : Type u} [Min α] {P : α → Prop} : Min (OrderedSubtype P) where
  min a b := ⟨Min.min a.val b.val, sorry⟩ -- TODO: Can only define this given min_eq_or.

public instance {α : Type u} [OrderData α] {P : α → Prop} : OrderData (OrderedSubtype P) where
  IsLE a b := OrderData.IsLE a.val b.val

section LE

public class LawfulOrderLE (α : Type u) [LE α] [OrderData α] where
  le_iff : ∀ a b : α, a ≤ b ↔ OrderData.IsLE a b

public instance {α : Type u} [LE α] [OrderData α] [LawfulOrderLE α] [PartialOrder α] :
    Std.Antisymm (fun a b : α => a ≤ b) where
  antisymm a b := by
    simp only [LawfulOrderLE.le_iff]
    apply PartialOrder.le_antisymm

public theorem le_refl {α : Type u} [LE α] [OrderData α] [LawfulOrderLE α] [Preorder α] (a : α) :
    a ≤ a := by
  simp [LawfulOrderLE.le_iff, Preorder.le_refl]

public theorem le_antisymm {α : Type u} [LE α] [Std.Antisymm (α := α) (· ≤ ·)] {a b : α}
    (hab : a ≤ b) (hba : b ≤ a) : a = b :=
  Std.Antisymm.antisymm _ _ hab hba

end LE

section Min

public class MinEqOr (α : Type u) [Min α] where
  min_eq_or : ∀ a b : α, min a b = a ∨ min a b = b

public class LawfulOrderInf (α : Type u) [Min α] [OrderData α] where
  le_min_iff : ∀ a b c : α, OrderData.IsLE a (min b c) ↔ OrderData.IsLE a b ∧ OrderData.IsLE a c

public class LawfulOrderMin (α : Type u) [Min α] [OrderData α] extends MinEqOr α, LawfulOrderInf α

public theorem min_eq_or {α : Type u} [Min α] [MinEqOr α] {a b : α} :
    min a b = a ∨ min a b = b :=
  MinEqOr.min_eq_or a b

public theorem le_min_iff {α : Type u} [LE α] [Min α] [OrderData α] [LawfulOrderInf α]
    [LawfulOrderLE α] {a b c : α} :
    a ≤ min b c ↔ a ≤ b ∧ a ≤ c := by
  simp [LawfulOrderLE.le_iff, LawfulOrderInf.le_min_iff]

end Min
