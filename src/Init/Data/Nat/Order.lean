module

prelude
import Init.Data.Nat.MinMax
public import Std.Classes.Ord.New.Factories

public instance : OrderData Nat := OrderData.ofLE Nat

public instance : LinearOrder Nat := by
  apply LinearOrder.ofLE
  · apply Nat.le_refl
  · apply Nat.le_antisymm
  · apply Nat.le_trans
  · apply Nat.le_total

public instance : LawfulOrderMin Nat := by
  apply LawfulOrderMin.ofLE
  · apply Nat.le_min
  · intro a b
    simp only [Nat.min_def]
    split <;> simp
