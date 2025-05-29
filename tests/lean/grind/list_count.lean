open List

set_option grind.warning false

variable [BEq α] [LawfulBEq α]

-- These tests should move back to `tests/lean/run/grind_list_count.lean` once fixed.

theorem count_pos_iff {a : α} {l : List α} : 0 < count a l ↔ a ∈ l := by
  induction l with grind -- fails, having proved `head = a` is false and `head == a` is true.

theorem one_le_count_iff {a : α} {l : List α} : 1 ≤ count a l ↔ a ∈ l := by
  induction l with grind -- fails, similarly

theorem count_eq_zero_of_not_mem {a : α} {l : List α} (h : a ∉ l) : count a l = 0 := by
  induction l with grind -- fails

theorem count_eq_zero {l : List α} : count a l = 0 ↔ a ∉ l := by
  induction l with grind -- fails

theorem count_filter {l : List α} (h : p a) : count a (filter p l) = count a l := by
  induction l with grind -- similarly

theorem count_le_count_map {β} [BEq β] [LawfulBEq β] {l : List α} {f : α → β} {x : α} :
    count x l ≤ count (f x) (map f l) := by
  induction l with grind

theorem count_erase {a b : α} {l : List α} : count a (l.erase b) = count a l - if b == a then 1 else 0 := by
  induction l with grind [-List.count_erase]
  -- fails with inconsistent equivalence clases:
  -- [] {head == a, false}
  -- [] {b == a, head == b, true}
