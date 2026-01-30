/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Init.Data.String.Pattern.Basic
public import Init.Data.Iterators.Consumers.Monadic.Loop
import Init.Data.String.Termination
public import Init.Data.Vector.Basic

set_option doc.verso true

/-!
This module defines the necessary instances to register {name}`String` and {name}`String.Slice`
with the pattern framework.
-/

public section

namespace String.Slice.Pattern

namespace ForwardSliceSearcher

def buildTable (pat : Slice) : Vector Nat pat.utf8ByteSize :=
  if h : pat.utf8ByteSize = 0 then
    #v[].cast h.symm
  else
    let arr := Array.emptyWithCapacity pat.utf8ByteSize
    let arr' := arr.push 0
    go arr' (by simp [arr']) (by simp [arr', arr]; omega) (by simp [arr', arr])
where
  go (table : Array Nat) (ht₀ : 0 < table.size) (ht : table.size ≤ pat.utf8ByteSize) (h : ∀ (i : Nat) hi, table[i]'hi ≤ i) :
      Vector Nat pat.utf8ByteSize :=
    if hs : table.size < pat.utf8ByteSize then
      let patByte := pat.getUTF8Byte ⟨table.size⟩ hs
      let dist := computeDistance patByte table ht h (table[table.size - 1])
        (by have := h (table.size - 1) (by omega); omega)
      let dist' := if pat.getUTF8Byte ⟨dist.1⟩ (by simp [Pos.Raw.lt_iff]; omega) = patByte then dist.1 + 1 else dist
      go (table.push dist') (by simp) (by simp; omega) (by
        intro i hi
        by_cases hi' : i = table.size
        · subst hi'
          simp [dist']
          have := dist.2
          split <;> omega
        · rw [Array.getElem_push_lt]
          · apply h
          · simp at hi
            omega)
    else
      Vector.mk table (by omega)

  computeDistance (patByte : UInt8) (table : Array Nat)
      (ht : table.size ≤ pat.utf8ByteSize)
      (h : ∀ (i : Nat) hi, table[i]'hi ≤ i) (guess : Nat) (hg : guess < table.size) :
      { n : Nat // n < table.size } :=
    if h' : guess = 0 ∨ pat.getUTF8Byte ⟨guess⟩ (by simp [Pos.Raw.lt_iff]; omega) = patByte then
      ⟨guess, hg⟩
    else
      have : table[guess - 1] < guess := by have := h (guess - 1) (by omega); omega
      computeDistance patByte table ht h table[guess - 1] (by omega)

theorem getElem_buildTable_le (pat : Slice) (i : Nat) (hi) : (buildTable pat)[i]'hi ≤ i := by
  rw [buildTable]
  split <;> rename_i h
  · simp [h] at hi
  · simp only [Array.emptyWithCapacity_eq, List.push_toArray, List.nil_append]
    suffices ∀ pat' table ht₀ ht h (i : Nat) hi, (buildTable.go pat' table ht₀ ht h)[i]'hi ≤ i from this ..
    intro pat' table ht₀ ht h i hi
    fun_induction buildTable.go with
    | case1 => assumption
    | case2 table ht₀ ht ht' ht'' => apply ht'

inductive _root_.String.Slice.Pattern.ForwardSliceSearcher (s : Slice) where
  | emptyBefore (pos : s.Pos)
  | emptyAt (pos : s.Pos) (h : pos ≠ s.endPos)
  | proper (needle : Slice) (table : Vector Nat needle.utf8ByteSize) (ht : table = buildTable needle)
      (stackPos : String.Pos.Raw) (needlePos : String.Pos.Raw) (hn : needlePos < needle.rawEndPos)
  | atEnd
deriving Inhabited

@[inline]
def iter (pat : Slice) (s : Slice) : Std.Iter (α := ForwardSliceSearcher s) (SearchStep s) :=
  if h : pat.utf8ByteSize = 0 then
    { internalState := .emptyBefore s.startPos }
  else
    { internalState := .proper pat (buildTable pat) rfl s.startPos.offset pat.startPos.offset
        (by simp [Pos.Raw.lt_iff]; omega) }

instance (s : Slice) : Std.Iterator (ForwardSliceSearcher s) Id (SearchStep s) where
  IsPlausibleStep it
    | .yield it' out | .skip it' =>
     match it.internalState with
      | .emptyBefore pos => (∃ h, it'.internalState = .emptyAt pos h) ∨ it'.internalState = .atEnd
      | .emptyAt pos h => ∃ newPos, pos < newPos ∧ it'.internalState = .emptyBefore newPos
      | .proper needle table ht stackPos needlePos hn =>
        (∃ newStackPos newNeedlePos hn,
          it'.internalState = .proper needle table ht newStackPos newNeedlePos hn ∧
            ((s.utf8ByteSize - newStackPos.byteIdx < s.utf8ByteSize - stackPos.byteIdx) ∨
              (newStackPos = stackPos ∧ newNeedlePos < needlePos))) ∨
        it'.internalState = .atEnd
      | .atEnd => False
    | .done => True
  step := fun ⟨iter⟩ =>
    match iter with
    | .emptyBefore pos =>
      let res := .matched pos pos
      if h : pos ≠ s.endPos then
        pure (.deflate ⟨.yield ⟨.emptyAt pos h⟩ res, by simp [h]⟩)
      else
        pure (.deflate ⟨.yield ⟨.atEnd⟩ res, by simp⟩)
    | .emptyAt pos h =>
      let res := .rejected pos (pos.next h)
      pure (.deflate ⟨.yield ⟨.emptyBefore (pos.next h)⟩ res, by simp⟩)
    | .proper needle table htable stackPos needlePos hn =>
      -- **Invariant 1:** we have already covered everything up until `stackPos - needlePos` (exclusive),
      -- with matches and rejections.
      -- **Invariant 2:** `stackPos - needlePos` is a valid position
      -- **Invariant 3:** the range from `stackPos - needlePos` to `stackPos` (exclusive) is a
      -- prefix of the pattern.
      if h₁ : stackPos < s.rawEndPos then
        let stackByte := s.getUTF8Byte stackPos h₁
        let patByte := needle.getUTF8Byte needlePos hn
        if stackByte = patByte then
          let nextStackPos := stackPos.inc
          let nextNeedlePos := needlePos.inc
          if h : nextNeedlePos = needle.rawEndPos then
            -- Safety: the section from `nextStackPos.decreaseBy needle.utf8ByteSize` to `nextStackPos`
            -- (exclusive) is exactly the needle, so it must represent a valid range.
            let res := .matched (s.pos! (nextStackPos.decreaseBy needle.utf8ByteSize)) (s.pos! nextStackPos)
            -- Invariants still satisfied
            pure (.deflate ⟨.yield ⟨.proper needle table htable nextStackPos 0
              (by simp [Pos.Raw.lt_iff] at hn ⊢; omega)⟩ res,
               by simpa using ⟨_, _, ⟨rfl, rfl⟩, by simp [Pos.Raw.lt_iff] at hn ⊢; omega,
                Or.inl (by simp [nextStackPos, Pos.Raw.lt_iff] at h₁ ⊢; omega)⟩⟩)
          else
            -- Invariants still satisfied
            pure (.deflate ⟨.skip ⟨.proper needle table htable nextStackPos nextNeedlePos
              (by simp [Pos.Raw.lt_iff, nextNeedlePos, Pos.Raw.ext_iff] at h hn ⊢; omega)⟩,
               by simpa using ⟨_, _, ⟨rfl, rfl⟩, by simp [nextNeedlePos, Pos.Raw.lt_iff, Pos.Raw.ext_iff] at h hn ⊢; omega,
                Or.inl (by simp [nextStackPos, Pos.Raw.lt_iff] at h₁ ⊢; omega)⟩⟩)
        else
          if hnp : needlePos.byteIdx = 0 then
            -- Safety: by invariant 2
            let basePos := s.pos! stackPos
            -- Since we report (mis)matches by code point and not by byte, missing in the first byte
            -- means that we should skip ahead to the next code point.
            let nextStackPos := s.findNextPos stackPos h₁
            let res := .rejected basePos nextStackPos
            -- Invariants still satisfied
            pure (.deflate ⟨.yield ⟨.proper needle table htable nextStackPos.offset 0
              (by simp [Pos.Raw.lt_iff] at hn ⊢; omega)⟩ res,
               by simpa using ⟨_, _, ⟨rfl, rfl⟩, by simp [Pos.Raw.lt_iff] at hn ⊢; omega,
                Or.inl (by
                  have := lt_offset_findNextPos h₁
                  have t₀ := (findNextPos _ _ h₁).isValidForSlice.le_utf8ByteSize
                  simp [nextStackPos, Pos.Raw.lt_iff] at this ⊢; omega)⟩⟩)
          else
            let newNeedlePos := table[needlePos.byteIdx - 1]'(by simp [Pos.Raw.lt_iff] at hn; omega)
            if newNeedlePos = 0 then
              -- Safety: by invariant 2
              let basePos := s.pos! (stackPos.unoffsetBy needlePos)
              -- Since we report (mis)matches by code point and not by byte, missing in the first byte
              -- means that we should skip ahead to the next code point.
              let nextStackPos := (s.pos? stackPos).getD (s.findNextPos stackPos h₁)
              let res := .rejected basePos nextStackPos
              -- Invariants still satisfied
              pure (.deflate ⟨.yield ⟨.proper needle table htable nextStackPos.offset 0
                (by simp [Pos.Raw.lt_iff] at hn ⊢; omega)⟩ res,
                 by simpa using ⟨_, _, ⟨rfl, rfl⟩, by simp [Pos.Raw.lt_iff] at hn ⊢; omega, by
                  simp only [pos?, Pos.Raw.isValidForSlice_eq_true_iff, nextStackPos]
                  split
                  · exact Or.inr (by simp [Pos.Raw.lt_iff]; omega)
                  · refine Or.inl ?_
                    have := lt_offset_findNextPos h₁
                    have t₀ := (findNextPos _ _ h₁).isValidForSlice.le_utf8ByteSize
                    simp [Pos.Raw.lt_iff] at this ⊢; omega⟩⟩)
            else
              let oldBasePos := s.pos! (stackPos.decreaseBy needlePos.byteIdx)
              let newBasePos := s.pos! (stackPos.decreaseBy newNeedlePos)
              let res := .rejected oldBasePos newBasePos
              -- Invariants still satisfied by definition of the prefix table
              pure (.deflate ⟨.yield ⟨.proper needle table htable stackPos ⟨newNeedlePos⟩
                (by
                  subst htable
                  have := getElem_buildTable_le needle (needlePos.byteIdx - 1) (by simp [Pos.Raw.lt_iff] at hn; omega)
                  simp [newNeedlePos, Pos.Raw.lt_iff] at hn ⊢
                  omega)⟩ res,
                by
                  simp only [proper.injEq, heq_eq_eq, true_and, exists_and_left, exists_prop,
                    reduceCtorEq, or_false]
                  refine ⟨_, _, ⟨rfl, rfl⟩, ?_, Or.inr ⟨rfl, ?_⟩⟩
                  all_goals
                    subst htable
                    have := getElem_buildTable_le needle (needlePos.byteIdx - 1) (by simp [Pos.Raw.lt_iff] at hn; omega)
                    simp [newNeedlePos, Pos.Raw.lt_iff] at hn ⊢
                    omega⟩)
      else
        if 0 < needlePos then
          let basePos := stackPos.unoffsetBy needlePos
          let res := .rejected (s.pos! basePos) s.endPos
          pure (.deflate ⟨.yield ⟨.atEnd⟩ res, by simp⟩)
        else
          pure (.deflate ⟨.done, by simp⟩)
    | .atEnd => pure (.deflate ⟨.done, by simp⟩)

private def toOption : ForwardSliceSearcher s → Option (Nat × Nat)
  | .emptyBefore pos => some (pos.remainingBytes, 1)
  | .emptyAt pos _ => some (pos.remainingBytes, 0)
  | .proper _ _ _ sp np _ => some (s.utf8ByteSize - sp.byteIdx, np.byteIdx)
  | .atEnd => none

private instance : WellFoundedRelation (ForwardSliceSearcher s) where
  rel := InvImage (Option.lt (Prod.Lex (· < ·) (· < ·))) ForwardSliceSearcher.toOption
  wf := by
    apply InvImage.wf
    apply Option.wellFounded_lt
    apply (Prod.lex _ _).wf

private def finitenessRelation :
    Std.Iterators.FinitenessRelation (ForwardSliceSearcher s) Id where
  Rel := InvImage WellFoundedRelation.rel (fun it => it.internalState)
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by
    simp_wf
    obtain ⟨step, h, h'⟩ := h
    cases step
    all_goals try
      cases h
      revert h'
      simp only [Std.IterM.IsPlausibleStep, Std.Iterator.IsPlausibleStep]
      match it.internalState with
      | .emptyBefore pos =>
        rintro (⟨h, h'⟩|h') <;> simp [h', ForwardSliceSearcher.toOption, Option.lt, Prod.lex_def]
      | .emptyAt pos h =>
        simp only [forall_exists_index, and_imp]
        intro x hx h
        simpa [h, ForwardSliceSearcher.toOption, Option.lt, Prod.lex_def,
          ← Pos.lt_iff_remainingBytes_lt]
      | .proper needle table ht stackPos needlePos hn =>
        rintro (⟨newStackPos, newNeedlePos, h₁, h₂, (h|⟨rfl, h⟩)⟩|h)
        · simp [h₂, ForwardSliceSearcher.toOption, Option.lt, Prod.lex_def, h]
        · simpa [h₂, ForwardSliceSearcher.toOption, Option.lt, Prod.lex_def, Pos.Raw.lt_iff]
        · simp [h, ForwardSliceSearcher.toOption, Option.lt]
      | .atEnd .. => simp
    · cases h

@[no_expose]
instance : Std.Iterators.Finite (ForwardSliceSearcher s) Id :=
  .of_finitenessRelation finitenessRelation

instance : Std.IteratorLoop (ForwardSliceSearcher s) Id Id :=
  .defaultImplementation

instance {pat : Slice} : ToForwardSearcher pat ForwardSliceSearcher where
  toSearcher := iter pat

@[inline]
def startsWith (pat : Slice) (s : Slice) : Bool :=
  if h : pat.utf8ByteSize ≤ s.utf8ByteSize then
    have hs := by
      simp [Pos.Raw.le_iff] at h ⊢
      omega
    have hp := by
      simp [Pos.Raw.le_iff]
    Internal.memcmpSlice s pat s.startPos.offset pat.startPos.offset pat.rawEndPos hs hp
  else
    false

@[inline]
def dropPrefix? (pat : Slice) (s : Slice) : Option s.Pos :=
  if startsWith pat s then
    some <| s.pos! <| pat.rawEndPos.offsetBy s.startPos.offset
  else
    none

instance {pat : Slice} : ForwardPattern pat where
  startsWith := startsWith pat
  dropPrefix? := dropPrefix? pat

instance {pat : String} : ToForwardSearcher pat ForwardSliceSearcher where
  toSearcher := iter pat.toSlice

instance {pat : String} : ForwardPattern pat where
  startsWith := startsWith pat.toSlice
  dropPrefix? := dropPrefix? pat.toSlice

end ForwardSliceSearcher

namespace BackwardSliceSearcher

@[inline]
def endsWith (pat : Slice) (s : Slice) : Bool :=
  if h : pat.utf8ByteSize ≤ s.utf8ByteSize then
    let sStart := s.endPos.offset.unoffsetBy pat.rawEndPos
    let patStart := pat.startPos.offset
    have hs := by
      simp [sStart, Pos.Raw.le_iff] at h ⊢
      omega
    have hp := by
      simp [patStart, Pos.Raw.le_iff] at h ⊢
    Internal.memcmpSlice s pat sStart patStart pat.rawEndPos hs hp
  else
    false

@[inline]
def dropSuffix? (pat : Slice) (s : Slice) : Option s.Pos :=
  if endsWith pat s then
    some <| s.pos! <| s.endPos.offset.unoffsetBy pat.rawEndPos
  else
    none

instance {pat : Slice} : BackwardPattern pat where
  endsWith := endsWith pat
  dropSuffix? := dropSuffix? pat

instance {pat : String} : BackwardPattern pat where
  endsWith := endsWith pat.toSlice
  dropSuffix? := dropSuffix? pat.toSlice

end BackwardSliceSearcher

end String.Slice.Pattern
