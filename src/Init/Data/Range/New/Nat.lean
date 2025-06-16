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

instance : UpwardEnumerableRange ⟨.closed, .closed⟩ Nat where
  init lowerBound := some lowerBound

instance : LawfulUpwardEnumerableRange ⟨.closed, .closed⟩ Nat where
  satisfiesUpperBound_of_le u a b hub hab := by
    rw [← LawfulUpwardEnumerableLE.le_iff] at hab
    exact Nat.le_trans hab hub
  satisfiesLowerBound_iff a l := by
    simp [← LawfulUpwardEnumerableLE.le_iff, UpwardEnumerableRange.init,
      HasRange.SatisfiesLowerBound]

instance : LawfulUpwardEnumerableRange ⟨.open, .closed⟩ Nat where
  satisfiesUpperBound_of_le u a b hub hab := by
    rw [← LawfulUpwardEnumerableLE.le_iff] at hab
    exact Nat.le_trans hab hub
  satisfiesLowerBound_iff a l := by
    simp [← LawfulUpwardEnumerableLE.le_iff, UpwardEnumerableRange.init,
      HasRange.SatisfiesLowerBound, UpwardEnumerable.succ?, Nat.lt_iff_add_one_le]

instance : LawfulUpwardEnumerableRange ⟨.unbounded, .closed⟩ Nat where
  satisfiesUpperBound_of_le u a b hub hab := by
    rw [← LawfulUpwardEnumerableLE.le_iff] at hab
    exact Nat.le_trans hab hub
  satisfiesLowerBound_iff a l := by
    simp [← LawfulUpwardEnumerableLE.le_iff, UpwardEnumerableRange.init,
      HasRange.SatisfiesLowerBound, Nat.lt_iff_add_one_le, Least?.least?]

instance : LawfulUpwardEnumerableRange ⟨.closed, .open⟩ Nat where
  satisfiesUpperBound_of_le u a b hub hab := by
    rw [← LawfulUpwardEnumerableLE.le_iff] at hab
    exact Nat.lt_of_le_of_lt hab hub
  satisfiesLowerBound_iff a l := by
    simp [← LawfulUpwardEnumerableLE.le_iff, UpwardEnumerableRange.init,
      HasRange.SatisfiesLowerBound]

instance : LawfulUpwardEnumerableRange ⟨.open, .open⟩ Nat where
  satisfiesUpperBound_of_le u a b hub hab := by
    rw [← LawfulUpwardEnumerableLE.le_iff] at hab
    exact Nat.lt_of_le_of_lt hab hub
  satisfiesLowerBound_iff a l := by
    simp [← LawfulUpwardEnumerableLE.le_iff, UpwardEnumerableRange.init,
      HasRange.SatisfiesLowerBound, UpwardEnumerable.succ?, Nat.lt_iff_add_one_le]

instance : LawfulUpwardEnumerableRange ⟨.unbounded, .open⟩ Nat where
  satisfiesUpperBound_of_le u a b hub hab := by
    rw [← LawfulUpwardEnumerableLE.le_iff] at hab
    exact Nat.lt_of_le_of_lt hab hub
  satisfiesLowerBound_iff a l := by
    simp [← LawfulUpwardEnumerableLE.le_iff, UpwardEnumerableRange.init,
      HasRange.SatisfiesLowerBound, Nat.lt_iff_add_one_le, Least?.least?]

instance : LawfulUpwardEnumerableRange ⟨.closed, .unbounded⟩ Nat where
  satisfiesUpperBound_of_le u a b hub hab := .intro
  satisfiesLowerBound_iff a l := by
    simp [← LawfulUpwardEnumerableLE.le_iff, UpwardEnumerableRange.init,
      HasRange.SatisfiesLowerBound]

instance : LawfulUpwardEnumerableRange ⟨.open, .unbounded⟩ Nat where
  satisfiesUpperBound_of_le u a b hub hab := .intro
  satisfiesLowerBound_iff a l := by
    simp [← LawfulUpwardEnumerableLE.le_iff, UpwardEnumerableRange.init,
      HasRange.SatisfiesLowerBound, UpwardEnumerable.succ?, Nat.lt_iff_add_one_le]

instance : LawfulUpwardEnumerableRange ⟨.unbounded, .unbounded⟩ Nat where
  satisfiesUpperBound_of_le u a b hub hab := .intro
  satisfiesLowerBound_iff a l := by
    simp [← LawfulUpwardEnumerableLE.le_iff, UpwardEnumerableRange.init,
      HasRange.SatisfiesLowerBound, Nat.lt_iff_add_one_le, Least?.least?]

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

instance : FinitelyEnumerableRange ⟨.closed, .closed⟩ Nat where
  enumeration upperBound := rangeRev (upperBound + 1)
  mem_enumeration_of_satisfiesUpperBound upperBound a h := by
    simp only [HasRange.SatisfiesUpperBound] at h
    apply mem_rangeRev
    exact Nat.lt_succ_of_le h

instance : FinitelyEnumerableRange ⟨.open, .closed⟩ Nat where
  enumeration upperBound := rangeRev (upperBound + 1)
  mem_enumeration_of_satisfiesUpperBound upperBound a h := by
    simp only [HasRange.SatisfiesUpperBound] at h
    apply mem_rangeRev
    exact Nat.lt_succ_of_le h

instance : FinitelyEnumerableRange ⟨.unbounded, .closed⟩ Nat where
  enumeration upperBound := rangeRev (upperBound + 1)
  mem_enumeration_of_satisfiesUpperBound upperBound a h := by
    simp only [HasRange.SatisfiesUpperBound] at h
    apply mem_rangeRev
    exact Nat.lt_succ_of_le h

instance : FinitelyEnumerableRange ⟨.closed, .open⟩ Nat where
  enumeration upperBound := rangeRev (upperBound + 1)
  mem_enumeration_of_satisfiesUpperBound upperBound a h := by
    simp only [HasRange.SatisfiesUpperBound] at h
    apply mem_rangeRev
    exact Nat.lt_succ_of_lt h

instance : FinitelyEnumerableRange ⟨.open, .open⟩ Nat where
  enumeration upperBound := rangeRev (upperBound + 1)
  mem_enumeration_of_satisfiesUpperBound upperBound a h := by
    simp only [HasRange.SatisfiesUpperBound] at h
    apply mem_rangeRev
    exact Nat.lt_succ_of_lt h

instance : FinitelyEnumerableRange ⟨.unbounded, .open⟩ Nat where
  enumeration upperBound := rangeRev (upperBound + 1)
  mem_enumeration_of_satisfiesUpperBound upperBound a h := by
    simp only [HasRange.SatisfiesUpperBound] at h
    apply mem_rangeRev
    exact Nat.lt_succ_of_lt h
