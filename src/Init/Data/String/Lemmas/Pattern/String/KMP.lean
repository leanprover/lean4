/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

prelude
public import Init.Data.String.Lemmas.Pattern.String.Basic
-- import Init.Data.ByteArray.Lemmas
import Init.Omega
import Init.ByCases

namespace String.Slice.Pattern

namespace ForwardSliceSearcher

/-- Predicate asserting that `pat[0...needlePos] = s[stackPos - needlePos...stackPos]`. -/
structure PartialMatch (pat s : ByteArray) (needlePos stackPos : Nat) : Prop where
  stackPos_le_size : stackPos ≤ s.size
  needlePos_le_size : needlePos ≤ pat.size
  needlePos_le_stackPos : needlePos ≤ stackPos
  getElem_eq (j) (hj : j < needlePos) : pat[j] = s[stackPos - needlePos + j]

theorem partialMatch_iff {pat s needlePos stackPos} : PartialMatch pat s needlePos stackPos ↔
    ∃ (h₁ : stackPos ≤ s.size) (h₂ : needlePos ≤ pat.size) (h₃ : needlePos ≤ stackPos),
      ∀ (j), (hj : j < needlePos) → pat[j] = s[stackPos - needlePos + j] :=
  ⟨fun ⟨h₁, h₂, h₃, h₄⟩ => ⟨h₁, h₂, h₃, h₄⟩, fun ⟨h₁, h₂, h₃, h₄⟩ => ⟨h₁, h₂, h₃, h₄⟩⟩

instance : Decidable (PartialMatch pat s needlePos stackPos) :=
  decidable_of_iff' _ partialMatch_iff

@[simp]
theorem partialMatch_zero {pat s : ByteArray} {stackPos : Nat} (h : stackPos ≤ s.size) :
    PartialMatch pat s 0 stackPos := by constructor <;> simp [h]

theorem partialMatch_add_one_add_one_iff {pat s : ByteArray} {stackPos needlePos : Nat} :
    PartialMatch pat s (needlePos + 1) (stackPos + 1) ↔
      PartialMatch pat s needlePos stackPos ∧ ∃ h₁ h₂, pat[needlePos]'h₁ = s[stackPos]'h₂ := by
  refine ⟨fun ⟨h₁, h₂, h₃, h₄⟩ => ?_, fun ⟨⟨h₁, h₂, h₃, h₄⟩, ⟨h₅, h₆, h₇⟩⟩ => ?_⟩
  · refine ⟨⟨by omega, by omega, by omega, fun j hj => ?_⟩, ⟨by omega, by omega, ?_⟩⟩
    · rw [h₄ _ (by omega)]
      congr 1
      omega
    · rw [h₄ _ (by omega)]
      congr 1
      omega
  · refine ⟨by omega, by omega, by omega, fun j hj => ?_⟩
    by_cases hj' : j < needlePos
    · rw [h₄ _ hj']
      congr 1
      omega
    · obtain rfl : j = needlePos := by omega
      rw [h₇]
      congr 1
      omega

theorem PartialMatch.partialMatch_of_le {pat s : ByteArray} {stackPos needlePos : Nat}
    (h : PartialMatch pat s needlePos stackPos) (newStackPos : Nat) (h' : newStackPos ≤ stackPos)
    (h'' : stackPos - newStackPos ≤ needlePos) : PartialMatch pat s (needlePos - (stackPos - newStackPos)) newStackPos := by
  rcases h with ⟨h₀, h₁, h₂, h₃⟩
  refine ⟨by omega, by omega, by omega, fun j hj => ?_⟩
  rw [h₃ j (by omega)]
  congr 1
  omega

theorem PartialMatch.partialMatch_iff {pat s : ByteArray} {stackPos needlePos : Nat}
    (h : PartialMatch pat s needlePos stackPos) {needlePos' : Nat} :
    PartialMatch pat pat needlePos' needlePos ↔
      needlePos' ≤ needlePos ∧ PartialMatch pat s needlePos' stackPos := by
  rcases h with ⟨h₀, h₀', h₀'', h₀'''⟩
  refine ⟨fun ⟨h₁, h₂, h₃, h₄⟩ => ?_, fun ⟨h₁, ⟨h₂, h₃, h₄, h₅⟩⟩ => ?_⟩
  · refine ⟨h₃, ⟨h₀, h₂, by omega, fun j hj => ?_⟩⟩
    rw [h₄ _ hj, h₀''' _ (by omega)]
    congr 1
    omega
  · refine ⟨h₀', h₃, h₁, fun j hj => ?_⟩
    rw [h₅ _ hj, h₀''' _ (by omega)]
    congr 1
    omega

theorem matchesAt_iff_partialMatch {pat s : Slice} (hpat : pat.isEmpty = false) {pos : s.Pos} :
    MatchesAt pat pos ↔ PartialMatch pat.copy.toByteArray s.copy.toByteArray
      pat.copy.toByteArray.size (pos.offset.byteIdx + pat.copy.toByteArray.size) := by
  rw [matchesAt_iff_getElem hpat]
  refine ⟨fun ⟨h, h'⟩ => ⟨h, Nat.le_refl _, by simp, fun j hj => by simp [h' j hj]⟩, fun h => ?_⟩
  exact ⟨h.stackPos_le_size, fun j hj => by simp [h.getElem_eq j hj]⟩

/-- `prefixFunction pat i …` is the maximum `k` such that `pat[0...k] = pat[stackPos - k + 1...=stackPos]`. -/
def prefixFunction (pat : ByteArray) (stackPos : Nat) (hst : stackPos < pat.size) : Nat :=
  go (stackPos + 1)
where go (k : Nat) : Nat :=
  if h : PartialMatch pat pat k (stackPos + 1) then
    k
  else
    have : k ≠ 0 := by rintro rfl; simp [partialMatch_zero (Nat.lt_iff_add_one_le.1 hst)] at h
    go (k - 1)

theorem prefixFunction.le_go_iff {pat : ByteArray} {stackPos : Nat} {hst : stackPos < pat.size} {k k'} :
    k ≤ prefixFunction.go pat stackPos hst k' ↔ ∃ k'', k ≤ k'' ∧ k'' ≤ k' ∧ PartialMatch pat pat k'' (stackPos + 1) := by
  fun_induction go with
  | case1 k' h =>
    exact ⟨fun h' => ⟨k', h', Std.le_refl _, h⟩, fun ⟨k'', h₁, h₂, _⟩ => Std.le_trans h₁ h₂⟩
  | case2 k' h h₀ ih =>
    rw [ih]
    refine ⟨fun ⟨k'', h₀, h₁, h₂⟩ => ⟨k'', h₀, by omega, h₂⟩, fun ⟨k'', h₀, h₁, h₂⟩ => ?_⟩
    have : k'' ≠ k' := by rintro rfl; contradiction
    exact ⟨k'', h₀, by omega, h₂⟩

theorem le_prefixFunction_iff {pat : ByteArray} {stackPos : Nat} {hst : stackPos < pat.size} :
    k ≤ prefixFunction pat stackPos hst ↔ ∃ k', k ≤ k' ∧ PartialMatch pat pat k' (stackPos + 1) := by
  rw [prefixFunction, prefixFunction.le_go_iff]
  exact ⟨fun ⟨k', h₀, h₁, h₂⟩ => ⟨k', h₀, h₂⟩,
    fun ⟨k', h₀, h₁⟩ => ⟨k', h₀, h₁.needlePos_le_stackPos, h₁⟩⟩

theorem prefixFunction_le_iff {pat : ByteArray} {stackPos : Nat} {hst : stackPos < pat.size} :
    prefixFunction pat stackPos hst ≤ k ↔ ∀ k', k < k' → ¬ PartialMatch pat pat k' (stackPos + 1) := by
  rw [Nat.le_iff_lt_add_one, ← Std.not_le, le_prefixFunction_iff]
  simp [Nat.le_iff_lt_add_one]

theorem prefixFunction_eq_iff {pat : ByteArray} {stackPos : Nat} {hst : stackPos < pat.size} :
    prefixFunction pat stackPos hst = k ↔
      PartialMatch pat pat k (stackPos + 1) ∧ ∀ k', k < k' → ¬ PartialMatch pat pat k' (stackPos + 1) := by
  rw [← Std.le_antisymm_iff, le_prefixFunction_iff, prefixFunction_le_iff, and_comm, and_congr_left_iff]
  refine fun h => ⟨fun ⟨k', h₀, h₁⟩ => ?_, fun h => ⟨_, Nat.le_refl _, h⟩⟩
  suffices ¬ k < k' by (obtain rfl : k = k' := by omega); assumption
  exact fun h' => h _ h' h₁

theorem PartialMatch.le_prefixFunction {pat : ByteArray} {stackPos needlePos : Nat}
    (h : PartialMatch pat pat needlePos stackPos) (h₀ : 0 < stackPos) :
    needlePos ≤ prefixFunction pat (stackPos - 1) (by have := h.stackPos_le_size; omega) := by
  rw [le_prefixFunction_iff]
  exact ⟨needlePos, Nat.le_refl _, by rwa [Nat.sub_add_cancel (by omega)]⟩

/--
These are the invariants satisfied by the KMP search iterator. They are sufficient to ensure that
the code does not panic and returns the correct result.
-/
structure Invariants (pat s : Slice) (needlePos stackPos : String.Pos.Raw) : Prop where
  isEmpty_eq_false : pat.isEmpty = false
  partialMatch : PartialMatch pat.copy.toByteArray s.copy.toByteArray needlePos.byteIdx stackPos.byteIdx
  isValid : (stackPos.unoffsetBy needlePos).IsValidForSlice s

/-
theorem PartialMatch.partialMatch_iff {pat s : ByteArray} {stackPos needlePos : Nat}
    (h : PartialMatch pat s needlePos stackPos) {needlePos' : Nat} :
    PartialMatch pat pat needlePos' needlePos ↔
      needlePos' ≤ needlePos ∧ PartialMatch pat s needlePos' stackPos := by
-/

theorem Invariants.not_matchesAt_of_prefixFunction_eq {pat s : Slice} {stackPos needlePos : String.Pos.Raw}
    (h : Invariants pat s needlePos stackPos)
    (h' : 0 < needlePos) {k : Nat} {hki} (hk : prefixFunction pat.copy.toByteArray (needlePos.byteIdx - 1) hki = k)
    (p : s.Pos) (hp₁ : stackPos.unoffsetBy needlePos ≤ p.offset) (hp₂ : p.offset < stackPos.unoffsetBy ⟨k⟩)
    -- {h₁ h₂}
    -- (hmism : s.getUTF8Byte stackPos h₁ ≠ pat.getUTF8Byte needlePos h₂)
    :
    ¬ MatchesAt pat p := by
  -- simp [getUTF8Byte_eq_getUTF8Byte_copy, String.getUTF8Byte] at hmism
  rw [matchesAt_iff_partialMatch h.isEmpty_eq_false]
  intro hpart
  simp only [Pos.Raw.le_iff, Pos.Raw.byteIdx_unoffsetBy, Nat.sub_le_iff_le_add, Pos.Raw.lt_iff,
    Pos.Raw.byteIdx_zero] at hp₁ hp₂ h'
  have := hpart.partialMatch_of_le stackPos.byteIdx (by omega) (by omega)
  have := hk ▸ (h.partialMatch.partialMatch_iff.2 ⟨by omega, this⟩).le_prefixFunction h'
  omega

-- def prefixFunction (b : ByteArray) (i : Nat) (hi : i < b.size) : Nat :=
--   go i
-- where go (k : Nat) : Nat :=
--   if h : PartialMatch b i hi k then
--     k
--   else
--     have : k ≠ 0 := by rintro rfl; simp_all
--     go (k - 1)

end ForwardSliceSearcher

end String.Slice.Pattern
