module

prelude
-- public import Std.Classes.Ord.New.Classes
-- import Init.SimpLemmas

public class X

instance : X := ⟨⟩

-- public def OrderData.ofLE (α : Type u) [LE α] : OrderData α where
--   IsLE := LE.le

-- instance {α : Type u} [LE α] :
--     haveI := OrderData.ofLE α
--     LawfulOrderLE α :=
--   letI := OrderData.ofLE α
--   { le_iff _ _ := by exact Iff.rfl }

-- public def LinearOrder.ofLE {α : Type u} [OrderData α] [LE α] [LawfulOrderLE α]
--     (le_refl : ∀ a : α, a ≤ a)
--     (le_antisymm : ∀ a b : α, a ≤ b → b ≤ a → a = b)
--     (le_trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c)
--     (le_total : ∀ a b : α, a ≤ b ∨ b ≤ a) :
--     LinearOrder α where
--   le_refl := by simpa [LawfulOrderLE.le_iff] using le_refl
--   le_antisymm := by simpa [LawfulOrderLE.le_iff] using le_antisymm
--   le_trans := by simpa [LawfulOrderLE.le_iff] using le_trans
--   le_total := by simpa [LawfulOrderLE.le_iff] using le_total
