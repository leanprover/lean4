/-!
# Test for auxiliary parent projections (diamond inheritance)

`getStuckMVar?` should detect stuck metavariables through auxiliary parent projections
created for diamond inheritance. Previously, these coercions were not registered as projections,
so `getStuckMVar?` would give up and TC synthesis was never triggered.
-/

class AddZero' (M : Type u_2) extends Zero M, Add M where

class AddMonoid' (M : Type u) extends Add M, AddZero' M where

instance : AddZero' Int where
instance : AddMonoid' Int where

theorem sub_nonneg' {α : Type u} [AddMonoid' α] [Sub α] [LE α] {a b : α} :
  0 ≤ a - b ↔ b ≤ a := sorry

-- This used to fail because `getStuckMVar?` could not find the stuck mvar
-- through `AddMonoid'.toAddZero'` (an auxiliary parent projection from diamond inheritance).
example (a b : Int) : 0 ≤ a - b ↔ b ≤ a := by rw [sub_nonneg']
