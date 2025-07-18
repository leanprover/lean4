module

prelude
public import Init.Data.Char.Basic
import Init.Data.Char.Lemmas
public import Init.Data.Order.Factories

open Std

public instance : OrderData Char := .ofLE Char

public instance : LinearOrder Char := by
  apply LinearOrder.ofLE
  case le_refl => apply Char.le_refl
  case le_antisymm => apply Char.le_antisymm
  case le_trans => apply Char.le_trans
  case le_total => apply Char.le_total

public instance : LawfulOrderLT Char where
  lt_iff a b := by
    simp [← Char.not_le, ← LawfulOrderLE.le_iff, Decidable.imp_iff_not_or, Std.Total.total]
