/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Init.Data.String.Pattern.Basic
public import Init.Data.Iterators.Internal.Termination
public import Init.Data.Iterators.Consumers.Monadic.Loop

set_option doc.verso true

/-!
This module defines the necessary instances to register {name}`String` and {name}`String.Slice`
with the pattern framework.
-/

public section

namespace String.Slice.Pattern

inductive ForwardSliceSearcher (s : Slice) where
  | emptyBefore (pos : s.Pos)
  | emptyAt (pos : s.Pos) (h : pos ≠ s.endPos)
  | proper (needle : Slice) (table : Array String.Pos.Raw) (stackPos : String.Pos.Raw) (needlePos : String.Pos.Raw)
  | atEnd
deriving Inhabited

namespace ForwardSliceSearcher

partial def buildTable (pat : Slice) : Array String.Pos.Raw :=
  if pat.utf8ByteSize == 0 then
    #[]
  else
    let arr := Array.emptyWithCapacity pat.utf8ByteSize
    let arr := arr.push 0
    go ⟨1⟩ arr
where
  go (pos : String.Pos.Raw) (table : Array String.Pos.Raw) :=
    if h : pos < pat.rawEndPos then
      let patByte := pat.getUTF8Byte pos h
      let distance := computeDistance table[table.size - 1]! patByte table
      let distance := if patByte = pat.getUTF8Byte! distance then distance.inc else distance
      go pos.inc (table.push distance)
    else
      table

  computeDistance (distance : String.Pos.Raw) (patByte : UInt8) (table : Array String.Pos.Raw) :
      String.Pos.Raw :=
    if distance > 0 && patByte != pat.getUTF8Byte! distance then
      computeDistance table[distance.byteIdx - 1]! patByte table
    else
      distance

@[inline]
def iter (s : Slice) (pat : Slice) : Std.Iter (α := ForwardSliceSearcher s) (SearchStep s) :=
  if pat.utf8ByteSize == 0 then
    { internalState := .emptyBefore s.startPos }
  else
    { internalState := .proper pat (buildTable pat) s.startPos.offset pat.startPos.offset }

partial def backtrackIfNecessary (pat : Slice) (table : Array String.Pos.Raw) (stackByte : UInt8)
    (needlePos : String.Pos.Raw) : String.Pos.Raw :=
  if needlePos != 0 && stackByte != pat.getUTF8Byte! needlePos then
    backtrackIfNecessary pat table stackByte table[needlePos.byteIdx - 1]!
  else
    needlePos

instance (s : Slice) : Std.Iterators.Iterator (ForwardSliceSearcher s) Id (SearchStep s) where
  IsPlausibleStep it
    | .yield it' out =>
      match it.internalState with
      | .emptyBefore pos => (∃ h, it'.internalState = .emptyAt pos h) ∨ it'.internalState = .atEnd
      | .emptyAt pos h => ∃ newPos, pos < newPos ∧ it'.internalState = .emptyBefore newPos
      | .proper needle table stackPos needlePos =>
        (∃ newStackPos newNeedlePos,
          stackPos < newStackPos ∧
          newStackPos ≤ s.rawEndPos ∧
          it'.internalState = .proper needle table newStackPos newNeedlePos) ∨
        it'.internalState = .atEnd
      | .atEnd => False
    | .skip _ => False
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
    | .proper needle table stackPos needlePos =>
      let rec findNext (startPos : String.Pos.Raw)
          (currStackPos : String.Pos.Raw) (needlePos : String.Pos.Raw) (h : stackPos ≤ currStackPos) :=
        if h1 : currStackPos < s.rawEndPos then
          let stackByte := s.getUTF8Byte currStackPos h1
          let needlePos := backtrackIfNecessary needle table stackByte needlePos
          let patByte := needle.getUTF8Byte! needlePos
          if stackByte != patByte then
            let nextStackPos := s.findNextPos currStackPos h1 |>.offset
            let res := .rejected (s.pos! startPos) (s.pos! nextStackPos)
            have hiter := by
              left
              exists nextStackPos
              have haux := lt_offset_findNextPos h1
              simp only [String.Pos.Raw.lt_iff, proper.injEq, true_and, exists_and_left, exists_eq', and_true,
                nextStackPos]
              constructor
              · simp [String.Pos.Raw.le_iff, String.Pos.Raw.lt_iff] at h haux ⊢
                omega
              · apply Pos.Raw.IsValidForSlice.le_utf8ByteSize
                apply Pos.isValidForSlice
            .deflate ⟨.yield ⟨.proper needle table nextStackPos needlePos⟩ res, hiter⟩
          else
            let needlePos := needlePos.inc
            if needlePos == needle.rawEndPos then
              let nextStackPos := currStackPos.inc
              let res := .matched (s.pos! startPos) (s.pos! nextStackPos)
              have hiter := by
                left
                exists nextStackPos
                simp only [Pos.Raw.byteIdx_inc, proper.injEq, true_and, exists_and_left,
                  exists_eq', and_true, nextStackPos, String.Pos.Raw.lt_iff]
                constructor
                · simp [String.Pos.Raw.le_iff] at h ⊢
                  omega
                · simp [String.Pos.Raw.le_iff, String.Pos.Raw.lt_iff] at h1 ⊢
                  omega
              .deflate ⟨.yield ⟨.proper needle table nextStackPos 0⟩ res, hiter⟩
            else
              have hinv := by
                simp [String.Pos.Raw.le_iff] at h ⊢
                omega
              findNext startPos currStackPos.inc needlePos hinv
        else
          if startPos != s.rawEndPos then
            let res := .rejected (s.pos! startPos) (s.pos! currStackPos)
            .deflate ⟨.yield ⟨.atEnd⟩ res, by simp⟩
          else
            .deflate ⟨.done, by simp⟩
        termination_by s.utf8ByteSize - currStackPos.byteIdx
        decreasing_by
          simp [String.Pos.Raw.lt_iff] at h1 ⊢
          omega

      findNext stackPos stackPos needlePos (by simp)
    | .atEnd => pure (.deflate ⟨.done, by simp⟩)

private def toOption : ForwardSliceSearcher s → Option (Nat × Nat)
  | .emptyBefore pos => some (s.utf8ByteSize - pos.offset.byteIdx, 1)
  | .emptyAt pos _ => some (s.utf8ByteSize - pos.offset.byteIdx, 0)
  | .proper _ _ sp _ => some (s.utf8ByteSize - sp.byteIdx, 0)
  | .atEnd => none

private instance : WellFoundedRelation (ForwardSliceSearcher s) where
  rel := InvImage (Option.lt (Prod.Lex (· < ·) (· < ·))) ForwardSliceSearcher.toOption
  wf := by
    apply InvImage.wf
    apply Option.wellFounded_lt
    apply (Prod.lex _ _).wf

private def finitenessRelation :
    Std.Iterators.FinitenessRelation (ForwardSliceSearcher s) Id where
  rel := InvImage WellFoundedRelation.rel (fun it => it.internalState)
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by
    simp_wf
    obtain ⟨step, h, h'⟩ := h
    cases step
    · cases h
      revert h'
      simp only [Std.Iterators.IterM.IsPlausibleStep, Std.Iterators.Iterator.IsPlausibleStep]
      match it.internalState with
      | .emptyBefore pos =>
        rintro (⟨h, h'⟩|h') <;> simp [h', ForwardSliceSearcher.toOption, Option.lt, Prod.lex_def]
      | .emptyAt pos h =>
        simp only [forall_exists_index, and_imp]
        intro x hx h
        have := x.isValidForSlice.le_utf8ByteSize
        simp [h, ForwardSliceSearcher.toOption, Option.lt, Prod.lex_def, Pos.lt_iff,
          Pos.Raw.lt_iff, Pos.Raw.le_iff] at hx ⊢ this
        omega
      | .proper needle table stackPos needlePos =>
        simp only [exists_and_left]
        rintro (⟨newStackPos, h₁, h₂, ⟨x, hx⟩⟩|h)
        · simp [hx, ForwardSliceSearcher.toOption, Option.lt, Prod.lex_def, Pos.Raw.lt_iff,
            Pos.Raw.le_iff] at ⊢ h₁ h₂
          omega
        · simp [h, ForwardSliceSearcher.toOption, Option.lt]
      | .atEnd .. => simp
    · cases h'
    · cases h

@[no_expose]
instance : Std.Iterators.Finite (ForwardSliceSearcher s) Id :=
  .of_finitenessRelation finitenessRelation

instance : Std.Iterators.IteratorLoop (ForwardSliceSearcher s) Id Id :=
  .defaultImplementation

instance : ToForwardSearcher Slice ForwardSliceSearcher where
  toSearcher := iter

@[inline]
def startsWith (s : Slice) (pat : Slice) : Bool :=
  if h : pat.utf8ByteSize ≤ s.utf8ByteSize then
    have hs := by
      simp [Pos.Raw.le_iff] at h ⊢
      omega
    have hp := by
      simp [Pos.Raw.le_iff]
    Internal.memcmp s pat s.startPos.offset pat.startPos.offset pat.rawEndPos hs hp
  else
    false

@[inline]
def dropPrefix? (s : Slice) (pat : Slice) : Option s.Pos :=
  if startsWith s pat then
    some <| s.pos! <| pat.rawEndPos.offsetBy s.startPos.offset
  else
    none

instance : ForwardPattern Slice where
  startsWith := startsWith
  dropPrefix? := dropPrefix?

instance : ToForwardSearcher String ForwardSliceSearcher where
  toSearcher slice pat := iter slice pat.toSlice

instance : ForwardPattern String where
  startsWith s pat := startsWith s pat.toSlice
  dropPrefix? s pat := dropPrefix? s pat.toSlice

end ForwardSliceSearcher

namespace BackwardSliceSearcher

@[inline]
def endsWith (s : Slice) (pat : Slice) : Bool :=
  if h : pat.utf8ByteSize ≤ s.utf8ByteSize then
    let sStart := s.endPos.offset.unoffsetBy pat.rawEndPos
    let patStart := pat.startPos.offset
    have hs := by
      simp [sStart, Pos.Raw.le_iff] at h ⊢
      omega
    have hp := by
      simp [patStart, Pos.Raw.le_iff] at h ⊢
    Internal.memcmp s pat sStart patStart pat.rawEndPos hs hp
  else
    false

@[inline]
def dropSuffix? (s : Slice) (pat : Slice) : Option s.Pos :=
  if endsWith s pat then
    some <| s.pos! <| s.endPos.offset.unoffsetBy pat.rawEndPos
  else
    none

instance : BackwardPattern Slice where
  endsWith := endsWith
  dropSuffix? := dropSuffix?

instance : BackwardPattern String where
  endsWith s pat := endsWith s pat.toSlice
  dropSuffix? s pat := dropSuffix? s pat.toSlice

end BackwardSliceSearcher

end String.Slice.Pattern
