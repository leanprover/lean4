prelude
import Init.Data.Range.New.Iteration

instance : UpwardEnumerable Nat where
  succ? n := some (n + 1)
  succMany? k n := some (n + k)

instance : Least? Nat where
  least? := some 0

instance : LawfulUpwardEnumerableLE Nat where
  le_iff a b := by
    constructor
    · intro h
      exact ⟨b - a, by simp [UpwardEnumerable.succMany?, Nat.add_sub_cancel' h]⟩
    · rintro ⟨n, hn⟩
      simp only [UpwardEnumerable.succMany?, Option.some.injEq] at hn
      rw [← hn]
      exact Nat.le_add_right _ _

instance : LawfulUpwardEnumerableLT Nat where
  lt_iff a b := by
    constructor
    · intro h
      refine ⟨b - a - 1, ?_⟩
      simp [UpwardEnumerable.succMany?]
      rw [Nat.sub_add_cancel, Nat.add_sub_cancel']
      · exact Nat.le_of_lt h
      · rwa [Nat.lt_iff_add_one_le, ← Nat.le_sub_iff_add_le'] at h
        exact Nat.le_trans (Nat.le_succ _) h
    · rintro ⟨n, hn⟩
      simp only [UpwardEnumerable.succMany?, Option.some.injEq] at hn
      rw [← hn]
      apply Nat.lt_add_of_pos_right
      apply Nat.zero_lt_succ

instance : LawfulUpwardEnumerable Nat where
  succMany?_zero := by simp [UpwardEnumerable.succMany?]
  succMany?_succ := by simp [UpwardEnumerable.succMany?, UpwardEnumerable.succ?, Bind.bind, Nat.add_assoc]
  ne_of_lt a b hlt := by
    rw [← LawfulUpwardEnumerableLT.lt_iff] at hlt
    exact Nat.ne_of_lt hlt

instance : LawfulUpwardEnumerableLowerBound .closed Nat where
  isValid_iff a l := by
    simp [← LawfulUpwardEnumerableLE.le_iff, UpwardEnumerableRange.init,
      SupportsLowerBound.IsSatisfied]

instance : LawfulUpwardEnumerableUpperBound .closed Nat where
  isValid_of_le u a b hub hab := by
    rw [← LawfulUpwardEnumerableLE.le_iff] at hab
    exact Nat.le_trans hab hub

instance : LawfulUpwardEnumerableLowerBound .open Nat where
  isValid_iff a l := by
    simp [← LawfulUpwardEnumerableLE.le_iff, UpwardEnumerableRange.init,
      SupportsLowerBound.IsSatisfied, UpwardEnumerable.succ?, Nat.lt_iff_add_one_le]

instance : LawfulUpwardEnumerableUpperBound .open Nat where
  isValid_of_le u a b hub hab := by
    rw [← LawfulUpwardEnumerableLE.le_iff] at hab
    exact Nat.lt_of_le_of_lt hab hub

instance : LawfulUpwardEnumerableLowerBound .unbounded Nat where
  isValid_iff a l := by
    simp [← LawfulUpwardEnumerableLE.le_iff, UpwardEnumerableRange.init,
      SupportsLowerBound.IsSatisfied, Nat.lt_iff_add_one_le, Least?.least?]

instance : LawfulUpwardEnumerableUpperBound .unbounded Nat where
  isValid_of_le _ _ _ _ _ := .intro

private def rangeRev (k : Nat) :=
  match k with
  | 0 => []
  | k + 1 => k :: rangeRev k

private theorem mem_rangeRev {k l : Nat} (h : l < k) : l ∈ rangeRev k := by
  induction k
  case zero => cases h
  case succ k ih =>
    rw [rangeRev]
    by_cases hl : l = k
    · simp [hl]
    · have : l < k := by
        apply Nat.lt_of_le_of_ne
        · exact Nat.le_of_lt_succ h
        · exact hl
      apply List.mem_cons_of_mem
      exact ih this

instance : FinitelyEnumerableRange .closed Nat where
  enumeration upperBound := rangeRev (upperBound + 1)
  mem_enumeration_of_satisfiesUpperBound upperBound a h := by
    simp only [SupportsUpperBound.IsSatisfied] at h
    apply mem_rangeRev
    exact Nat.lt_succ_of_le h

instance : FinitelyEnumerableRange .open Nat where
  enumeration upperBound := rangeRev (upperBound + 1)
  mem_enumeration_of_satisfiesUpperBound upperBound a h := by
    simp only [SupportsUpperBound.IsSatisfied] at h
    apply mem_rangeRev
    exact Nat.lt_succ_of_lt h
