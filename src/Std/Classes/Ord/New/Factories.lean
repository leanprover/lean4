module

prelude
public import Std.Classes.Ord.New.Classes
import Init.SimpLemmas

public def OrderData.ofLE (α : Type u) [LE α] : OrderData α where
  IsLE := LE.le

public instance {α : Type u} [LE α] :
    haveI := OrderData.ofLE α
    LawfulOrderLE α :=
  letI := OrderData.ofLE α
  { le_iff _ _ := by exact Iff.rfl }

public def LinearOrder.ofLE {α : Type u} [OrderData α] [LE α] [LawfulOrderLE α]
    (le_refl : ∀ a : α, a ≤ a)
    (le_antisymm : ∀ a b : α, a ≤ b → b ≤ a → a = b)
    (le_trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c)
    (le_total : ∀ a b : α, a ≤ b ∨ b ≤ a) :
    LinearOrder α where
  le_refl := by simpa [LawfulOrderLE.le_iff] using le_refl
  le_antisymm := by simpa [LawfulOrderLE.le_iff] using le_antisymm
  le_trans := by simpa [LawfulOrderLE.le_iff] using le_trans
  le_total := by simpa [LawfulOrderLE.le_iff] using le_total

public def LawfulOrderInf.ofLE {α : Type u} [OrderData α] [Min α] [LE α] [LawfulOrderLE α]
    (le_min_iff : ∀ a b c : α, a ≤ Min.min b c ↔ a ≤ b ∧ a ≤ c) : LawfulOrderInf α where
  le_min_iff := by simpa [LawfulOrderLE.le_iff] using le_min_iff

public def MinEqOr.ofLE {α : Type u} [OrderData α] [Min α] [LE α] [LawfulOrderLE α]
    (min_eq_or : ∀ a b : α, min a b = a ∨ min a b = b) : MinEqOr α where
  min_eq_or := by simpa [LawfulOrderLE.le_iff] using min_eq_or

public def LawfulOrderMin.ofLE {α : Type u} [OrderData α] [Min α] [LE α] [LawfulOrderLE α]
    (le_min_iff : ∀ a b c : α, a ≤ Min.min b c ↔ a ≤ b ∧ a ≤ c)
    (min_eq_or : ∀ a b : α, min a b = a ∨ min a b = b) : LawfulOrderMin α where
  toLawfulOrderInf := .ofLE le_min_iff
  toMinEqOr := .ofLE min_eq_or
