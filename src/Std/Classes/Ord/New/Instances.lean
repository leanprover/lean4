module

prelude
public import Std.Classes.Ord.New.Comparable
import Init.Data.Nat.Lemmas

instance : BLE Nat where
  LE a b := a ≤ b

instance : BLT Nat where
  LT a b := a < b

instance : ComputablyComparable Nat := .ofOrd {}

instance : LawfulComparable Nat where
  lt_iff_le_not_ge a b := by omega
  eq_lt_iff_lt a b := by
    simp []
