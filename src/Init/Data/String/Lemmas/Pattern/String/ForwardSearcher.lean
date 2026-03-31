/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

prelude
public import Init.Data.String.Lemmas.Pattern.String.Basic
public import Init.Data.String.Pattern.String
public import Init.Data.String.Slice
public import Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Search
import all Init.Data.String.Pattern.String
import Init.Data.String.Lemmas.IsEmpty
import Init.Data.Vector.Lemmas
import Init.Data.Iterators.Lemmas.Basic
import Init.Data.Iterators.Lemmas.Consumers.Collect
import Init.Data.String.Lemmas.Basic
import Init.Data.ByteArray.Lemmas
import Init.Data.String.OrderInstances

/-!
# Verification of KMP string search

In this file, we instantiate `LawfulToForwardSearcherModel` for `Slice` patterns, which amounts to
verifying that our implementation of KMP string search in `Init.Data.String.Pattern.String` is
correct.
-/

namespace String.Slice.Pattern.Model

namespace ForwardSliceSearcher

open Pattern.ForwardSliceSearcher

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
    · simp [h₄ j (by omega), Nat.add_sub_add_right]
    · simp [h₄ needlePos (by omega), Nat.add_sub_add_right,
        Nat.sub_add_cancel (Nat.add_le_add_iff_right.1 h₃)]
  · refine ⟨by omega, by omega, by omega, fun j hj => ?_⟩
    by_cases hj' : j < needlePos
    · simp [h₄ _ hj', Nat.add_sub_add_right]
    · obtain rfl : j = needlePos := by omega
      simp [h₇, Nat.add_sub_add_right, h₃]

theorem PartialMatch.partialMatch_of_le {pat s : ByteArray} {stackPos needlePos : Nat}
    (h : PartialMatch pat s needlePos stackPos) (newStackPos : Nat) (h' : newStackPos ≤ stackPos)
    (h'' : stackPos - newStackPos ≤ needlePos) :
    PartialMatch pat s (needlePos - (stackPos - newStackPos)) newStackPos := by
  rcases h with ⟨h₀, h₁, h₂, h₃⟩
  refine ⟨by omega, by omega, by omega, fun j hj => ?_⟩
  rw [h₃ j (by omega)]
  congr 1
  omega

/--
This is the key lemma for the correctness of KMP. Given a partial match of `pat` in `s`, it shows
that all shorter partial matches of `pat` in `s` ending at the same position are described by
partial matches of `pat` in itself.
-/
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
      pat.copy.toByteArray.size (pos.copy.offset.byteIdx + pat.copy.toByteArray.size) := by
  rw [matchesAt_iff_getElem hpat]
  refine ⟨fun ⟨h, h'⟩ => ⟨h, Nat.le_refl _, by omega, fun j hj => by simp [h' j hj]⟩, fun h => ?_⟩
  exact ⟨h.stackPos_le_size, fun j hj => by simp [h.getElem_eq j hj]⟩

theorem PartialMatch.isValidForSlice {pat s : Slice} (hpat : pat.isEmpty = false)
    {stackPos : Pos.Raw}
    (h : PartialMatch pat.copy.toByteArray s.copy.toByteArray pat.utf8ByteSize
      (stackPos.unoffsetBy s.startInclusive.offset).byteIdx)
    (h' : (stackPos.unoffsetBy pat.rawEndPos).IsValidForSlice s) : stackPos.IsValidForSlice s := by
  have hle_start := Pos.Raw.le_iff.1 h'.offset_startInclusive_le
  have hle_np := h.needlePos_le_stackPos
  simp only [Pos.Raw.byteIdx_unoffsetBy, size_toByteArray, utf8ByteSize_copy,
    Slice.byteIdx_rawEndPos] at hle_start hle_np
  have : (stackPos.unoffsetBy s.startInclusive.offset).byteIdx =
      (s.pos _ h').copy.offset.byteIdx + pat.copy.toByteArray.size := by
    simp only [Pos.Raw.byteIdx_unoffsetBy, Slice.Pos.offset_copy, size_toByteArray,
      utf8ByteSize_copy, offset_pos, Slice.byteIdx_rawEndPos]
    omega
  have h₀ : stackPos = (stackPos.unoffsetBy pat.rawEndPos).increaseBy pat.utf8ByteSize := by
    simp only [Pos.Raw.ext_iff, Pos.Raw.byteIdx_increaseBy, Pos.Raw.byteIdx_unoffsetBy,
      Slice.byteIdx_rawEndPos]
    omega
  rw [this, utf8ByteSize_eq_size_toByteArray_copy, ← matchesAt_iff_partialMatch hpat,
    matchesAt_iff_isLongestMatchAt hpat] at h
  obtain ⟨h, -⟩ := h
  rwa [h₀]

theorem PartialMatch.isLongestMatchAt
    {pat s : Slice} (hpat : pat.isEmpty = false)
    {stackPos : Pos.Raw}
    (h : PartialMatch pat.copy.toByteArray s.copy.toByteArray pat.utf8ByteSize
      (stackPos.unoffsetBy s.startInclusive.offset).byteIdx)
    (h' : (stackPos.unoffsetBy pat.rawEndPos).IsValidForSlice s) :
    IsLongestMatchAt pat (s.pos _ h') (s.pos _ (h.isValidForSlice hpat h')) := by
  have hle_start := Pos.Raw.le_iff.1 h'.offset_startInclusive_le
  have hle_np := h.needlePos_le_stackPos
  simp only [Pos.Raw.byteIdx_unoffsetBy, size_toByteArray, utf8ByteSize_copy,
    Slice.byteIdx_rawEndPos] at hle_start hle_np
  have : (stackPos.unoffsetBy s.startInclusive.offset).byteIdx =
      (s.pos _ h').copy.offset.byteIdx + pat.copy.toByteArray.size := by
    simp only [Pos.Raw.byteIdx_unoffsetBy, Slice.Pos.offset_copy, size_toByteArray,
      utf8ByteSize_copy, offset_pos, Slice.byteIdx_rawEndPos]
    omega
  have h₀ : stackPos = (stackPos.unoffsetBy pat.rawEndPos).increaseBy pat.utf8ByteSize := by
    simp only [Pos.Raw.ext_iff, Pos.Raw.byteIdx_increaseBy, Pos.Raw.byteIdx_unoffsetBy,
      Slice.byteIdx_rawEndPos]
    omega
  rw [this, utf8ByteSize_eq_size_toByteArray_copy, ← matchesAt_iff_partialMatch hpat,
    matchesAt_iff_isLongestMatchAt hpat] at h
  conv in s.pos stackPos _ => simp +singlePass [h₀]
  exact h.2

/--
`prefixFunction pat i …` is the maximum `k` such that `pat[0...k] = pat[stackPos - k + 1...=stackPos]`.

Using the implementation given here, computing a table of `prefixFunction pat i` for `i` in
`0...pat.size` would take cubic time, but we will later show that the `buildTable` function, which
runs in linear time, also computes this table.
-/
def prefixFunction (pat : ByteArray) (stackPos : Nat) (hst : stackPos < pat.size) : Nat :=
  go stackPos
where go (k : Nat) : Nat :=
  if h : PartialMatch pat pat k (stackPos + 1) then
    k
  else
    have : k ≠ 0 := by rintro rfl; simp [partialMatch_zero (Nat.lt_iff_add_one_le.1 hst)] at h
    go (k - 1)

theorem prefixFunction.le_go_iff {pat : ByteArray} {stackPos : Nat} {hst : stackPos < pat.size} {k k'} :
    k ≤ prefixFunction.go pat stackPos hst k' ↔
      ∃ k'', k ≤ k'' ∧ k'' ≤ k' ∧ PartialMatch pat pat k'' (stackPos + 1) := by
  fun_induction go with
  | case1 k' h =>
    exact ⟨fun h' => ⟨k', h', Std.le_refl _, h⟩, fun ⟨k'', h₁, h₂, _⟩ => Std.le_trans h₁ h₂⟩
  | case2 k' h h₀ ih =>
    rw [ih]
    refine ⟨fun ⟨k'', h₀, h₁, h₂⟩ => ⟨k'', h₀, by omega, h₂⟩, fun ⟨k'', h₀, h₁, h₂⟩ => ?_⟩
    have : k'' ≠ k' := by rintro rfl; contradiction
    exact ⟨k'', h₀, by omega, h₂⟩

theorem le_prefixFunction_iff {pat : ByteArray} {stackPos : Nat} {hst : stackPos < pat.size} :
    k ≤ prefixFunction pat stackPos hst ↔
      ∃ k', k ≤ k' ∧ k' ≤ stackPos ∧ PartialMatch pat pat k' (stackPos + 1) := by
  rw [prefixFunction, prefixFunction.le_go_iff]

theorem prefixFunction_le_iff {pat : ByteArray} {stackPos : Nat} {hst : stackPos < pat.size} :
    prefixFunction pat stackPos hst ≤ k ↔
      ∀ k', k < k' → k' ≤ stackPos → ¬ PartialMatch pat pat k' (stackPos + 1) := by
  rw [Nat.le_iff_lt_add_one, ← Std.not_le, le_prefixFunction_iff]
  simp [Nat.le_iff_lt_add_one]

theorem prefixFunction_eq_iff {pat : ByteArray} {stackPos : Nat} {hst : stackPos < pat.size} :
    prefixFunction pat stackPos hst = k ↔
      k ≤ stackPos ∧ PartialMatch pat pat k (stackPos + 1) ∧ ∀
        k', k < k' → k' ≤ stackPos → ¬ PartialMatch pat pat k' (stackPos + 1) := by
  rw [← Std.le_antisymm_iff, le_prefixFunction_iff, prefixFunction_le_iff, and_comm,
    ← and_assoc, and_congr_left_iff]
  refine fun h =>
    ⟨fun ⟨k', h₀, h₁, h₂⟩ => ⟨by omega, ?_⟩, fun ⟨h'₁, h'₂⟩ => ⟨_, Nat.le_refl _, h'₁, h'₂⟩⟩
  suffices ¬ k < k' by (obtain rfl : k = k' := by omega); assumption
  exact fun h' => h _ h' h₁ h₂

theorem PartialMatch.le_prefixFunction {pat : ByteArray} {stackPos needlePos : Nat}
    (h : PartialMatch pat pat needlePos stackPos) (h₀ : 0 < stackPos)
    (h₁ : needlePos ≤ stackPos - 1) :
    needlePos ≤ prefixFunction pat (stackPos - 1) (by have := h.stackPos_le_size; omega) := by
  rw [le_prefixFunction_iff]
  exact ⟨needlePos, Nat.le_refl _, h₁, by rwa [Nat.sub_add_cancel (by omega)]⟩

theorem partialMatch_prefixFunction (pat : ByteArray) (stackPos : Nat) (hst) :
    PartialMatch pat pat (prefixFunction pat stackPos hst) (stackPos + 1) :=
  (prefixFunction_eq_iff.1 rfl).2.1

theorem partialMatch_prefixFunction_sub_one {pat : ByteArray} {stackPos : Nat} {hst}
    (h : 0 < stackPos) :
    PartialMatch pat pat (prefixFunction pat (stackPos - 1) hst) stackPos := by
  rw (occs := [2]) [(by omega : stackPos = stackPos - 1 + 1)]
  exact partialMatch_prefixFunction ..

theorem prefixFunction_le {pat : ByteArray} {stackPos : Nat} {hst} :
    prefixFunction pat stackPos hst ≤ stackPos :=
  (prefixFunction_eq_iff.1 rfl).1

theorem prefixFunction_sub_one_lt {pat : ByteArray} {stackPos : Nat} {hst} (h : 0 < stackPos) :
    prefixFunction pat (stackPos - 1) hst < stackPos := by
  have := prefixFunction_le (hst := hst)
  omega

theorem prefixFunction_le_prefixFunction_sub_one_add_one {pat : ByteArray} {stackPos : Nat} {hst}
    (h₀ : 0 < stackPos) :
    prefixFunction pat stackPos hst ≤ prefixFunction pat (stackPos - 1) (by omega) + 1 := by
  rw [prefixFunction_le_iff]
  refine fun k hk hk' hpart => ?_
  rw [(by omega : k = k - 1 + 1), partialMatch_add_one_add_one_iff] at hpart
  have := hpart.1.le_prefixFunction h₀ (by omega)
  omega

/--
This is an implementation of `prefixFunction` that follows the efficient procedure employed by
the `buildTable` function.
-/
def prefixFunctionRecurrence (pat : ByteArray) (stackPos : Nat) (hst : stackPos < pat.size)
    (guess : Nat) (hg : guess < stackPos) : Nat :=
  if pat[guess] = pat[stackPos] then
    guess + 1
  else if h : guess = 0 then
    0
  else
    have : (prefixFunction pat (guess - 1) (by omega)) < guess := by
      have := prefixFunction_le (pat := pat) (stackPos := guess - 1) (hst := by omega)
      omega
    prefixFunctionRecurrence pat stackPos hst (prefixFunction pat (guess - 1) (by omega)) (by omega)

@[simp]
theorem prefixFunction_zero {b hi} : prefixFunction b 0 hi = 0 :=
  Nat.le_zero.1 prefixFunction_le

theorem prefixFunctionRecurrence_eq_prefixFunction {pat : ByteArray} {stackPos : Nat}
    {hst : stackPos < pat.size} {guess : Nat} {hg : guess < stackPos}
    (h : prefixFunction pat stackPos (by omega) ≤ guess + 1)
    (hpa : PartialMatch pat pat guess stackPos) :
    prefixFunctionRecurrence pat stackPos hst guess hg = prefixFunction pat stackPos hst := by
  fun_induction prefixFunctionRecurrence with
  | case1 g hg heq =>
    refine Std.le_antisymm (le_prefixFunction_iff.2 ⟨g + 1, Nat.le_refl _, by omega, ?_⟩) h
    exact partialMatch_add_one_add_one_iff.2 ⟨hpa, ⟨_, _, heq⟩⟩
  | case2 hg h' =>
    simp only [eq_comm (a := 0)]
    suffices prefixFunction pat stackPos hst ≠ 1 by omega
    intro heq
    rw [prefixFunction_eq_iff] at heq
    simp [heq.2.1.getElem_eq 0 Nat.zero_lt_one] at h'
  | case3 g hg heq hg₀ hlt ih =>
    apply ih
    · simp only [prefixFunction_le_iff]
      refine fun k h hk' hpart => ?_
      have hpx := hpart.le_prefixFunction (by omega) (by omega)
      simp only [Nat.add_one_sub_one] at hpx
      rw [(by omega : k = k - 1 + 1), partialMatch_add_one_add_one_iff] at hpart
      obtain ⟨hp₁, ⟨_, _, hp₂⟩⟩ := hpart
      have := hpa.partialMatch_iff.2 ⟨by omega, hp₁⟩
      have := this.le_prefixFunction (by omega)
      suffices k - 1 ≠ g by omega
      rintro rfl
      simp [hp₂] at heq
    · exact (hpa.partialMatch_iff.1 (partialMatch_prefixFunction_sub_one (by omega))).2

/-- Predicate that an array is a correct precomputation of the prefix function. -/
structure IsTable (b : ByteArray) (v : Array Nat) : Prop where
  size_le : v.size ≤ b.size
  eq_prefixFunction (i : Nat) (hi) : v[i]'hi = prefixFunction b i (by omega)

@[simp]
theorem isTable_empty : IsTable ByteArray.empty #[] where
  size_le := by simp
  eq_prefixFunction := by simp

theorem isTable_singleton {b : ByteArray} (hb : 1 ≤ b.size) : IsTable b #[0] where
  size_le := by simp [hb]
  eq_prefixFunction := by simp +contextual

theorem IsTable.push {b : ByteArray} {v : Array Nat} (h : IsTable b v) {d : Nat}
    (hle : v.size + 1 ≤ b.size)
    (hd : d = prefixFunction b v.size (by omega)) :
    IsTable b (v.push d) where
  size_le := by simpa using hle
  eq_prefixFunction i hi := by
    rw [Array.getElem_push]
    split <;> rename_i hi'
    · rw [h.eq_prefixFunction]
    · rw [Array.size_push] at hi
      obtain rfl : i = v.size := by omega
      exact hd

private theorem getUTF8ByteRel_eq_copy_getUTF8Byte {s : Slice} {p : Pos.Raw} {h : p < s.rawEndPos} :
    s.getUTF8ByteRel p h = s.copy.getUTF8Byte p (by rwa [rawEndPos_copy]) := by
  simp only [getUTF8ByteRel, Slice.getUTF8Byte_copy, Slice.getUTF8Byte]

set_option backward.isDefEq.respectTransparency false in
theorem computeDistance_eq_prefixFunctionRecurrence {s : Slice} (i : Nat)
    (hi : i < s.copy.toByteArray.size) {patByte : UInt8}
    (hpat : patByte = s.copy.toByteArray[i])
    (table : Array Nat) {ht} (ht' : IsTable s.copy.toByteArray table) {h guess hg hg'} :
    (buildTable.computeDistance s patByte table ht h guess hg').1 =
      prefixFunctionRecurrence s.copy.toByteArray i (by omega) guess hg := by
  cases hpat
  fun_induction prefixFunctionRecurrence with
  | case1 =>
    rw [buildTable.computeDistance, if_pos]
    simp [getUTF8ByteRel_eq_copy_getUTF8Byte, String.getUTF8Byte, *]
  | case2 =>
    rw [buildTable.computeDistance, if_neg, dif_pos]
    · rfl
    · simp [getUTF8ByteRel_eq_copy_getUTF8Byte, String.getUTF8Byte, *]
  | case3 g hg h₁ h₂ h₃ ih =>
    rw [buildTable.computeDistance, if_neg, dif_neg h₂]
    · simp only [ht'.eq_prefixFunction, ih]
    · simp [getUTF8ByteRel_eq_copy_getUTF8Byte, String.getUTF8Byte, *]

theorem isTable_buildTableGo {pat : Slice} {table : Array Nat} {ht₀ ht h}
    (ht' : IsTable pat.copy.toByteArray table) :
    IsTable pat.copy.toByteArray (buildTable.go pat table ht₀ ht h).1 := by
  fun_induction buildTable.go with
  | case1 t ht₀ ht h hlt patByte dist ih =>
    refine ih (ht'.push (by simp; omega) ?_)
    simp only [getUTF8ByteRel_eq_copy_getUTF8Byte, String.getUTF8Byte,
      ht'.eq_prefixFunction, dist, patByte]
    rw [computeDistance_eq_prefixFunctionRecurrence _ _ rfl _ ht',
      prefixFunctionRecurrence_eq_prefixFunction]
    · exact prefixFunction_le_prefixFunction_sub_one_add_one ht₀
    · exact partialMatch_prefixFunction_sub_one ht₀
    · exact prefixFunction_sub_one_lt ht₀
  | case2 t ht₀ ht h hlt => simpa

theorem isTable_buildTable {pat : Slice} :
    IsTable pat.copy.toByteArray (buildTable pat).toArray := by
  rw [buildTable]
  split
  · simp [String.toByteArray_eq_empty_iff.2 (by rwa [Slice.copy_eq_empty_iff, Slice.isEmpty_iff])]
  · exact isTable_buildTableGo (by simpa using isTable_singleton (by simp; omega))

@[simp]
theorem getElem_buildTable {pat : Slice} {i hi} :
    (buildTable pat)[i]'hi = prefixFunction pat.copy.toByteArray i (by simpa) := by
  rw [← Vector.getElem_toArray (h := by simpa), isTable_buildTable.eq_prefixFunction]

/--
These are the invariants satisfied by the KMP search iterator. They are sufficient to ensure that
the code does not panic and returns the correct result.
-/
structure Invariants (pat s : Slice) (needlePos stackPos : String.Pos.Raw) : Prop where
  isEmpty_eq_false : pat.isEmpty = false
  partialMatch : PartialMatch pat.copy.toByteArray s.copy.toByteArray
    needlePos.byteIdx (stackPos.unoffsetBy s.startInclusive.offset).byteIdx
  isValidForSlice' : needlePos = 0 → stackPos.IsValidForSlice s

theorem Invariants.inc {pat s : Slice} {stackPos needlePos : String.Pos.Raw}
    (h₀ : Invariants pat s needlePos stackPos) (h₁ h₂)
    (h : pat.getUTF8ByteRel needlePos h₁ = s.getUTF8Byte stackPos h₂) :
    Invariants pat s needlePos.inc stackPos.inc where
  isEmpty_eq_false := h₀.isEmpty_eq_false
  partialMatch := by
    simp only [Pos.Raw.byteIdx_unoffsetBy, Pos.Raw.byteIdx_inc]
    have hle : s.startInclusive.offset.byteIdx ≤ stackPos.byteIdx := by
      by_cases hn : needlePos = 0
      · exact Pos.Raw.le_iff.1 (h₀.isValidForSlice' hn).offset_startInclusive_le
      · have := h₀.partialMatch.needlePos_le_stackPos
        simp only [Pos.Raw.byteIdx_unoffsetBy, Pos.Raw.ext_iff, Pos.Raw.byteIdx_zero] at this hn
        omega
    rw [show stackPos.byteIdx + 1 - s.startInclusive.offset.byteIdx =
      (stackPos.byteIdx - s.startInclusive.offset.byteIdx) + 1 from by omega]
    simp only [getUTF8ByteRel_eq_copy_getUTF8Byte,
      Slice.getUTF8Byte_eq_getUTF8Byte_copy (Pos.Raw.le_iff.2 hle),
      String.getUTF8Byte, Pos.Raw.byteIdx_unoffsetBy] at h
    exact partialMatch_add_one_add_one_iff.2 ⟨by simpa [Pos.Raw.byteIdx_unoffsetBy] using
      h₀.partialMatch, ⟨_, _, h⟩⟩
  isValidForSlice' := by simp

theorem Invariants.isValidForSlice {pat s : Slice} {needlePos stackPos : String.Pos.Raw}
    (h : Invariants pat s needlePos stackPos) :
    (stackPos.unoffsetBy needlePos).IsValidForSlice s := by
  by_cases hn : needlePos = 0
  · cases hn
    simpa using h.isValidForSlice' rfl
  · simp only [Pos.Raw.ext_iff, Pos.Raw.byteIdx_zero] at hn
    rw [Pos.Raw.isValidForSlice_iff_isUTF8FirstByte, Classical.or_iff_not_imp_left]
    intro hst
    have hle_st := h.partialMatch.needlePos_le_stackPos
    have hle_sz := h.partialMatch.stackPos_le_size
    simp only [Pos.Raw.byteIdx_unoffsetBy, size_toByteArray, utf8ByteSize_copy,
      utf8ByteSize_eq] at hle_st hle_sz
    refine ⟨?_, ?_⟩
    · simp only [Pos.Raw.ext_iff, Pos.Raw.byteIdx_unoffsetBy, size_toByteArray,
        utf8ByteSize_copy, Pos.Raw.lt_iff, Pos.Raw.le_iff, gt_iff_lt] at ⊢ hst
      omega
    · have hle_start : s.startInclusive.offset ≤ stackPos.unoffsetBy needlePos := by
        simp only [Pos.Raw.le_iff, Pos.Raw.byteIdx_unoffsetBy]; omega
      refine ⟨by simp only [Pos.Raw.lt_iff, Pos.Raw.byteIdx_unoffsetBy]; omega, ?_⟩
      simp only [getUTF8Byte_eq_getUTF8Byte_copy hle_start,
        String.getUTF8Byte, Pos.Raw.byteIdx_unoffsetBy]
      have : (stackPos.byteIdx - needlePos.byteIdx) - s.startInclusive.offset.byteIdx =
          (stackPos.byteIdx - s.startInclusive.offset.byteIdx) - needlePos.byteIdx := by omega
      simp only [this]
      have hge := h.partialMatch.getElem_eq 0 (by omega)
      simp only [Pos.Raw.byteIdx_unoffsetBy] at hge
      simp +singlePass only [← Nat.add_zero
        ((stackPos.byteIdx - s.startInclusive.offset.byteIdx) - needlePos.byteIdx), ← hge]
      exact pat.copy.isValidUTF8.isUTF8FirstByte_getElem_zero ..

theorem Invariants.offset {pat s : Slice} {pos : s.Pos} (hpat : pat.isEmpty = false) :
    Invariants pat s 0 pos.offset where
  isEmpty_eq_false := hpat
  partialMatch := partialMatch_zero (by
    simp only [Pos.Raw.byteIdx_unoffsetBy, size_toByteArray, utf8ByteSize_copy, utf8ByteSize_eq]
    have := Pos.Raw.le_iff.1 pos.isValidForSlice.offset_startInclusive_le
    have := Pos.Raw.le_iff.1 pos.isValidForSlice.le_offset_endExclusive
    omega)
  isValidForSlice' _ := pos.isValidForSlice

/-- The start of the window, as a valid position in `s.` -/
def Invariants.base {pat s : Slice} {needlePos stackPos : String.Pos.Raw}
    (h : Invariants pat s needlePos stackPos) : s.Pos :=
  s.pos _ h.isValidForSlice

theorem Invariants.zero_of_eq {pat s : Slice} {stackPos needlePos : String.Pos.Raw}
    (h : Invariants pat s needlePos stackPos) (h' : needlePos = pat.rawEndPos) :
    Invariants pat s 0 stackPos := by
  cases h'
  refine ⟨h.isEmpty_eq_false, partialMatch_zero h.partialMatch.stackPos_le_size, fun _ => ?_⟩
  exact h.partialMatch.isValidForSlice h.isEmpty_eq_false h.isValidForSlice

theorem Invariants.isLongestMatchAt {pat s : Slice} {stackPos needlePos : String.Pos.Raw}
    (h : Invariants pat s needlePos stackPos) (h' : needlePos = pat.rawEndPos) :
    IsLongestMatchAt pat h.base (h.zero_of_eq h').base := by
  cases h'
  exact h.partialMatch.isLongestMatchAt h.isEmpty_eq_false h.isValidForSlice

set_option backward.isDefEq.respectTransparency false in
theorem Invariants.not_matchesAt_of_prefixFunction_eq {pat s : Slice}
    {stackPos needlePos : String.Pos.Raw} (h : Invariants pat s needlePos stackPos)
    {k : Nat} {hki} (hk : prefixFunction pat.copy.toByteArray (needlePos.byteIdx - 1) hki = k)
    (p : s.Pos) (hp₁ : stackPos.unoffsetBy needlePos ≤ p.offset)
    (hp₂ : p.offset < stackPos.unoffsetBy ⟨k⟩)
    {h₁ h₂} (hmism : s.getUTF8Byte stackPos h₁ ≠ pat.getUTF8ByteRel needlePos h₂) :
    ¬ MatchesAt pat p := by
  have hstart_le_st : s.startInclusive.offset ≤ stackPos := by
    by_cases hn : needlePos = 0
    · exact (h.isValidForSlice' hn).offset_startInclusive_le
    · have := h.partialMatch.needlePos_le_stackPos
      simp only [Pos.Raw.le_iff, Pos.Raw.byteIdx_unoffsetBy, Pos.Raw.ext_iff,
        Pos.Raw.byteIdx_zero] at this hn ⊢; omega
  simp only [getUTF8ByteRel_eq_copy_getUTF8Byte, getUTF8Byte_eq_getUTF8Byte_copy hstart_le_st,
    String.getUTF8Byte, ne_eq] at hmism
  rw [matchesAt_iff_partialMatch h.isEmpty_eq_false]
  intro hpart
  have hstart_le_p := Pos.Raw.le_iff.1 p.isValidForSlice.offset_startInclusive_le
  have hstart_le_st' := Pos.Raw.le_iff.1 hstart_le_st
  have hcsp : (stackPos.unoffsetBy s.startInclusive.offset).byteIdx =
      stackPos.byteIdx - s.startInclusive.offset.byteIdx := by
    simp [Pos.Raw.byteIdx_unoffsetBy]
  have hcpp : p.copy.offset.byteIdx = p.offset.byteIdx - s.startInclusive.offset.byteIdx := by
    simp [Slice.Pos.offset_copy, Pos.Raw.byteIdx_unoffsetBy]
  simp only [Pos.Raw.le_iff, Pos.Raw.byteIdx_unoffsetBy, Nat.sub_le_iff_le_add,
    Pos.Raw.lt_iff] at hp₁ hp₂
  by_cases hin : stackPos.byteIdx - p.offset.byteIdx ≤ needlePos.byteIdx - 1
  · have := hpart.partialMatch_of_le
      (stackPos.unoffsetBy s.startInclusive.offset).byteIdx (by omega) (by omega)
    have := hk ▸ (h.partialMatch.partialMatch_iff.2 ⟨by omega, this⟩).le_prefixFunction
      (by omega) (by omega)
    omega
  · obtain rfl : stackPos = needlePos.offsetBy p.offset := by
      simpa [Pos.Raw.ext_iff, Pos.Raw.byteIdx_offsetBy] using by omega
    have hlt_np : needlePos.byteIdx < pat.copy.toByteArray.size := by
      have := Pos.Raw.lt_iff.1 h₂
      simpa [byteIdx_rawEndPos, utf8ByteSize_copy, size_toByteArray] using this
    have hge := hpart.getElem_eq needlePos.byteIdx hlt_np
    simp only [Pos.Raw.byteIdx_unoffsetBy, Pos.Raw.byteIdx_offsetBy, Slice.Pos.offset_copy,
      size_toByteArray, utf8ByteSize_copy] at hge hmism
    simp only [Nat.add_sub_cancel] at hge
    have heq : p.offset.byteIdx - s.startInclusive.offset.byteIdx + needlePos.byteIdx =
        p.offset.byteIdx + needlePos.byteIdx - s.startInclusive.offset.byteIdx := by
      clear hge hmism hpart hcsp; omega
    simp only [heq] at hge
    exact hmism hge.symm

theorem Invariants.of_prefixFunction_eq {pat s : Slice} {stackPos needlePos : String.Pos.Raw}
    (h : Invariants pat s needlePos stackPos)
    (h' : needlePos ≠ 0) {k : Nat} {hki}
    (hk : prefixFunction pat.copy.toByteArray (needlePos.byteIdx - 1) hki = k) (hk₀ : 0 < k) :
    Invariants pat s ⟨k⟩ stackPos := by
  refine ⟨h.isEmpty_eq_false, ?_, by simp [Nat.pos_iff_ne_zero.1 hk₀]⟩
  have := partialMatch_prefixFunction (hst := hki)
  rw [Nat.sub_add_cancel (by simp at h'; omega)] at this
  exact hk ▸ (h.partialMatch.partialMatch_iff.1 this).2

theorem Invariants.isValidSearchFrom_toList {pat s : Slice} {stackPos needlePos : String.Pos.Raw}
    (it : Std.Iter (α := ForwardSliceSearcher s) (SearchStep s))
    (h : Invariants pat s needlePos stackPos)
    {table ht hn}
    (heq : it = Std.Iter.mk (.proper pat table ht stackPos needlePos hn))
    {p : s.Pos} (hp : p = h.base) :
    IsValidSearchFrom pat p it.toList := by
  induction it using Std.Iter.inductSteps generalizing p stackPos needlePos with | step it ihy ihs
  cases heq
  cases hp
  rw [Std.Iter.toList_eq_match_step]
  generalize hit' : (Std.Iter.mk (α := ForwardSliceSearcher s)
    (.proper pat table ht stackPos needlePos hn)).step = it'

  have hit'' := congrArg Subtype.val hit'
  have plausible := it'.property
  simp only [Std.Iter.step_eq, ne_eq, Std.Iter.toIterM] at hit''
  split at hit'' <;> rename_i h₁
  · split at hit'' <;> rename_i h₂
    · split at hit'' <;> rename_i h₃
      · -- Case 1: matched the full pattern
        simp only [Id.run_pure, Std.Shrink.inflate_deflate, Std.IterM.Step.toPure_yield,
          Std.PlausibleIterStep.yield, Std.IterM.toIter_mk] at hit''
        have hinc := h.inc _ _ h₂.symm
        have hzero := hinc.zero_of_eq h₃
        rw [s.pos!_eq_pos hinc.isValidForSlice, s.pos!_eq_pos (hzero.isValidForSlice' rfl)] at hit''
        simp only [← hit'', Pos.Raw.inc_unoffsetBy_inc] at ⊢ plausible
        apply IsValidSearchFrom.matched_of_eq (ihy plausible hzero rfl rfl) _ rfl
        simpa [base] using hinc.isLongestMatchAt h₃

      · -- Case 2: matched the next character, but not yet the full pattern
        simp only [Id.run_pure, Std.Shrink.inflate_deflate, Std.IterM.Step.toPure_skip,
          Std.PlausibleIterStep.skip, Std.IterM.toIter_mk] at hit''
        simp only [← hit''] at ⊢ plausible
        exact ihs plausible (h.inc _ _ h₂.symm) rfl (by simp [base])

    · split at hit'' <;> rename_i h₃
      · -- Case 3: mismatch at the start of the pattern -> jump to next position
        simp only [Id.run_pure, Std.Shrink.inflate_deflate, Std.IterM.Step.toPure_yield,
          Std.PlausibleIterStep.yield, Std.IterM.toIter_mk] at hit''
        cases h₃
        rw [s.pos!_eq_pos (h.isValidForSlice' rfl)] at hit''
        simp only [← hit''] at ⊢ plausible
        apply IsValidSearchFrom.mismatched_of_eq _ (by simp [base]) _ (by simp [base])
        · exact ihy plausible (.offset h.isEmpty_eq_false) rfl rfl
        · simp only [base, Pos.Raw.unoffsetBy_zero, Pos.le_iff, offset_pos, lt_posGT_iff]
          intro pos hp₁ hp₂
          obtain rfl : stackPos = pos.offset := Std.le_antisymm hp₁ hp₂
          have hle := (h.isValidForSlice' rfl).offset_startInclusive_le
          simpa [matchesAt_iff_getElem h.isEmpty_eq_false] using fun h' => ⟨0, by simpa,
            by simpa [getUTF8ByteRel_eq_copy_getUTF8Byte,
              Slice.getUTF8Byte_eq_getUTF8Byte_copy hle,
              String.getUTF8Byte, Pos.Raw.byteIdx_unoffsetBy] using Ne.symm h₂⟩

      · cases ht
        simp only [getElem_buildTable] at hit''

        split at hit'' <;> rename_i h₄
        · -- Case 4: mismatch in the middle of the pattern, and no common prefix ->
          -- jump to next position if not at the start of the character
          simp only [Id.run_pure, Std.Shrink.inflate_deflate, Std.IterM.Step.toPure_yield,
            Std.PlausibleIterStep.yield, Std.IterM.toIter_mk] at hit''
          rw [s.pos!_eq_pos h.isValidForSlice] at hit''
          simp only [← hit''] at ⊢ plausible
          apply IsValidSearchFrom.mismatched_of_eq _ _ _ (by simp [base])
          · exact ihy plausible (.offset h.isEmpty_eq_false) rfl rfl
          · have := h.partialMatch.needlePos_le_stackPos
            simp only [Pos.Raw.ext_iff, Pos.Raw.byteIdx_zero, base, lt_posGE_iff, offset_pos,
              Pos.Raw.lt_iff, Pos.Raw.byteIdx_unoffsetBy, gt_iff_lt] at ⊢ h₃ this
            omega
          · simp only [base, lt_posGE_iff]
            exact fun p hp₁ hp₂ => not_matchesAt_of_prefixFunction_eq h h₄ _ hp₁ hp₂ h₂

        · -- Case 5: mismatch in the middle of the pattern with a common prefix
          simp only [Id.run_pure, Std.Shrink.inflate_deflate, Std.IterM.Step.toPure_yield,
            Std.PlausibleIterStep.yield, Std.IterM.toIter_mk] at hit''
          rw [s.pos!_eq_pos h.isValidForSlice,
            s.pos!_eq_pos (h.of_prefixFunction_eq h₃ rfl (by omega)).isValidForSlice] at hit''
          simp only [← hit''] at ⊢ plausible
          apply IsValidSearchFrom.mismatched_of_eq _ _ _ (by simp [base])
          · exact ihy plausible (h.of_prefixFunction_eq h₃ rfl (by omega)) rfl rfl
          · have h₅ := h.partialMatch.needlePos_le_stackPos
            simp [base, Pos.lt_iff, Pos.Raw.ext_iff] at ⊢ h₃ h₅
            apply Pos.Raw.unoffsetBy_lt_unoffsetBy_of_le_of_lt
            all_goals exact Std.lt_of_le_of_lt prefixFunction_le (by simp [Pos.Raw.lt_iff]; omega)
          · exact fun p hp₁ hp₂ => not_matchesAt_of_prefixFunction_eq h rfl _ hp₁ hp₂ h₂

  · split at hit'' <;> rename_i h₂
    · -- Case 6: so close to the end that we cannot match anymore -> reject, then done
      simp only [Id.run_pure, Std.Shrink.inflate_deflate, Std.IterM.Step.toPure_yield,
        Std.PlausibleIterStep.yield, Std.IterM.toIter_mk] at hit''
      rw [s.pos!_eq_pos h.isValidForSlice] at hit''
      simp only [← hit''] at ⊢ plausible
      apply IsValidSearchFrom.mismatched_of_eq _ _ _ (by simp [base])
      · rw [Std.Iter.toList_eq_match_step, Std.Iter.step_eq]
        simpa [Std.Iter.toIterM] using IsValidSearchFrom.endPos
      · simp only [Pos.Raw.lt_iff, Pos.Raw.byteIdx_unoffsetBy, base, Pos.lt_iff,
          offset_pos, offset_endPos] at ⊢ h₂
        omega
      · refine fun p hp₁ hp₂ hm => ?_
        have := le_of_matchesAt h.isEmpty_eq_false hm
        have hstart_le_st : s.startInclusive.offset.byteIdx ≤ stackPos.byteIdx := by
          by_cases hn : needlePos = 0
          · exact Pos.Raw.le_iff.1 (h.isValidForSlice' hn).offset_startInclusive_le
          · have := h.partialMatch.needlePos_le_stackPos
            simp only [Pos.Raw.byteIdx_unoffsetBy, Pos.Raw.ext_iff,
              Pos.Raw.byteIdx_zero] at this hn; omega
        have hstart_le_p := Pos.Raw.le_iff.1 p.isValidForSlice.offset_startInclusive_le
        have hpat_ne : 0 < pat.utf8ByteSize := by
          have h' := h.isEmpty_eq_false; simp [isEmpty_eq] at h'; omega
        simp only [base, Pos.le_iff, offset_pos, Pos.Raw.le_iff, Pos.Raw.byteIdx_unoffsetBy,
          Nat.sub_le_iff_le_add, Pos.Raw.byteIdx_increaseBy, byteIdx_rawEndPos,
          Nat.not_le, Slice.Pos.offset_copy, Slice.offset_endPos,
          utf8ByteSize_eq] at hp₁ this h₁ hpat_ne
        omega

    · --  Case 7: reached the end with empty partial match -> done
      simp only [base, ← hit'', Id.run_pure, Std.Shrink.inflate_deflate, Std.IterM.Step.toPure_done,
        Std.PlausibleIterStep.done, Std.IterM.toIter_mk]
      apply IsValidSearchFrom.endPos_of_eq (Std.le_antisymm (Pos.le_endPos _) _) rfl
      simpa [Pos.Raw.le_iff, Pos.le_iff, Pos.Raw.lt_iff] using h₂

theorem Invariants.start (pat s : Slice) (h : pat.isEmpty = false) :
    Invariants pat s 0 s.startPos.offset where
  isEmpty_eq_false := h
  partialMatch := by
    simp only [Slice.offset_startPos, Pos.Raw.byteIdx_unoffsetBy, Nat.sub_self,
      Pos.Raw.byteIdx_zero]
    exact partialMatch_zero (by simp)
  isValidForSlice' _ := s.startPos.isValidForSlice

theorem Invariants.base_start {pat s : Slice} (h : pat.isEmpty = false) :
    (Invariants.start pat s h).base = s.startPos := by
  simp only [base, Slice.Pos.ext_iff, offset_pos, Pos.Raw.ext_iff,
    Pos.Raw.byteIdx_unoffsetBy, Pos.Raw.byteIdx_zero, Nat.sub_zero, Slice.offset_startPos]

public theorem lawfulToForwardSearcherModel {pat : Slice} (hpat : pat.isEmpty = false) :
    LawfulToForwardSearcherModel pat where
  isValidSearchFrom_toList s := by
    simp only [ToForwardSearcher.toSearcher]
    rw [iter, dif_neg (by simpa [isEmpty_eq] using hpat)]
    rw (occs := [1]) [← Invariants.base_start hpat]
    apply Invariants.isValidSearchFrom_toList _ _ rfl rfl

@[simp]
public theorem toList_atEnd_eq {s : Slice} :
    (Std.Iter.mk (.atEnd : ForwardSliceSearcher s)).toList = [] := by
  rw [Std.Iter.toList_eq_match_step]
  simp [Std.Iter.step_eq]

@[simp]
public theorem toList_emptyAt_eq (s : Slice) (pos : s.Pos) (h : pos ≠ s.endPos) :
    (Std.Iter.mk (.emptyAt pos h : ForwardSliceSearcher s)).toList =
      .rejected pos (pos.next h) ::
        (Std.Iter.mk (.emptyBefore (pos.next h) : ForwardSliceSearcher s)).toList := by
  rw [Std.Iter.toList_eq_match_step]
  simp [Std.Iter.step_eq]

public theorem toList_emptyBefore_eq (s : Slice) (pos : s.Pos) :
    (Std.Iter.mk (.emptyBefore pos : ForwardSliceSearcher s)).toList =
      if h : pos = s.endPos then
        [.matched pos pos]
      else
        .matched pos pos ::
          (Std.Iter.mk (.emptyAt pos h : ForwardSliceSearcher s)).toList := by
  rw [Std.Iter.toList_eq_match_step, Std.Iter.step_eq]
  by_cases h : pos = s.endPos
  · simp [h]
  · rw [dif_neg h, Std.Iter.toList_eq_match_step]
    simp [Std.Iter.step_eq, h]

public theorem toSearcher_of_isEmpty {pat : Slice} (hpat : pat.isEmpty = true) (s : Slice) :
    ToForwardSearcher.toSearcher pat s =
      Std.Iter.mk (.emptyBefore s.startPos : ForwardSliceSearcher s) := by
  simp only [ToForwardSearcher.toSearcher, iter,
    dif_pos (show pat.utf8ByteSize = 0 from by simpa [isEmpty_eq] using hpat)]

end ForwardSliceSearcher

namespace ForwardStringSearcher

public theorem lawfulToForwardSearcherModel {pat : String} (hpat : pat ≠ "") :
    LawfulToForwardSearcherModel pat where
  isValidSearchFrom_toList s := by
    simpa [toSearcher_eq, isValidSearchFrom_iff_isValidSearchFrom_toSlice] using
      (ForwardSliceSearcher.lawfulToForwardSearcherModel (by simpa)).isValidSearchFrom_toList (pat := pat.toSlice) (s := s)

public theorem toSearcher_empty (s : Slice) : ToForwardSearcher.toSearcher "" s =
      Std.Iter.mk (.emptyBefore s.startPos : ForwardSliceSearcher s) := by
  simp only [ToForwardSearcher.toSearcher, ForwardSliceSearcher.iter,
    dif_pos (show "".toSlice.utf8ByteSize = 0 from by decide)]

end ForwardStringSearcher

end Pattern.Model

public theorem contains_string_eq_contains_toSlice {pat : String} {s : Slice} :
    s.contains pat = s.contains pat.toSlice :=
  (rfl)

public theorem find?_string_eq_find?_toSlice {pat : String} {s : Slice} :
    s.find? pat = s.find? pat.toSlice :=
  (rfl)

public theorem Pos.find?_string_eq_find?_toSlice {pat : String} {s : Slice} {p : s.Pos} :
    p.find? pat = p.find? pat.toSlice :=
  (rfl)

end String.Slice
