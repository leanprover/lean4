module

prelude
import Std.Classes.Ord.New.Instances

theorem Comparable.compare_isLE [Comparable α] [Ord α] [LawfulComparable α] [LawfulOrd α] {a b : α} :
    (compare a b).isLE ↔ a ≤ b := by
  simp [Ordering.isLE_iff_ne_gt, ← LawfulOrd.compare_eq_compare, LawfulComparable.eq_gt_iff_gt,
    LawfulComparable.le_iff_not_gt]

theorem Comparable.compare_isGE [Comparable α] [Ord α] [LawfulComparable α] [LawfulOrd α] {a b : α} :
    (compare a b).isGE ↔ b ≤ a := by
  simp [Ordering.isGE_iff_ne_lt, ← LawfulOrd.compare_eq_compare, LawfulComparable.eq_lt_iff_lt,
    LawfulComparable.le_iff_not_gt]

theorem Comparable.le_total [Comparable α] [LawfulComparable α] {a b : α} :
    a ≤ b ∨ b ≤ a := by
  open scoped Classical.Order in
  rw [← compare_isLE, ← compare_isGE]
  cases compare a b <;> simp

theorem Comparable.compare_eq_lt [Comparable α] [Ord α] [LawfulComparable α] [LawfulOrd α]
    [LawfulOrd α] {a b : α} : compare a b = .lt ↔ a < b := by
  simpa [LawfulOrd.compare_eq_compare] using LawfulComparable.eq_lt_iff_lt a b
