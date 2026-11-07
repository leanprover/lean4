/-!
Tests the `Std.LinearOrderPackage Char` instance: it provides `Min` and `Max` together with all the
lawfulness classes, and it reuses the existing `LE`, `LT`, `BEq` and `Ord` instances on `Char`
instead of introducing new ones.
-/

/-! The order instances and their lawfulness classes are available. -/

example : Std.LinearOrderPackage Char := inferInstance
example : Std.IsLinearOrder Char := inferInstance
example : Std.LawfulOrderLT Char := inferInstance
example : Std.LawfulOrderOrd Char := inferInstance
example : Std.LawfulOrderBEq Char := inferInstance
example : Std.LawfulOrderMin Char := inferInstance
example : Std.LawfulOrderMax Char := inferInstance
example : Std.LawfulOrderLeftLeaningMin Char := inferInstance
example : Std.LawfulOrderLeftLeaningMax Char := inferInstance
example : Std.TransOrd Char := inferInstance
example : Std.LawfulEqOrd Char := inferInstance

/-! The package does not introduce instance diamonds. -/

example : (inferInstance : Std.LinearOrderPackage Char).toLE = Char.instLE := by
  with_reducible_and_instances rfl
example : (inferInstance : Std.LinearOrderPackage Char).toLT = Char.instLT := by
  with_reducible_and_instances rfl
example : (inferInstance : Std.LinearOrderPackage Char).toBEq = instBEqOfDecidableEq := by
  with_reducible_and_instances rfl
example : (inferInstance : Std.LinearOrderPackage Char).toOrd = instOrdChar := by
  with_reducible_and_instances rfl

/-! The usual order lemmas apply. -/

example (a b : Char) : a ≤ b ∨ b ≤ a := Std.le_total
example (a b : Char) : ¬ a < b ↔ b ≤ a := Std.not_lt
example (a b : Char) : compare a b = .lt ↔ a < b := Std.compare_eq_lt
example (a b : Char) : compare a b = .eq ↔ a = b := Std.compare_eq_eq_iff_eq
example (a b : Char) : min a b = if a ≤ b then a else b := Std.min_eq_ite
example (a b : Char) : max a b = if b ≤ a then a else b := Std.max_eq_ite
example (a b : Char) : min a b ≤ max a b := Std.le_trans Std.min_le_left Std.left_le_max

/-! `min` and `max` evaluate both in the kernel and at runtime. -/

example : min 'a' 'b' = 'a' := by decide
example : max 'a' 'b' = 'b' := by decide
example : min 'β' 'α' = 'α' := by decide
example : max 'β' 'α' = 'β' := by decide

#guard min 'a' 'b' = 'a'
#guard max 'a' 'b' = 'b'
#guard min 'β' 'α' = 'α'
#guard max 'β' 'α' = 'β'
