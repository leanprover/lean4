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
  | empty (pos : s.Pos)
  | proper (needle : Slice) (table : Array String.Pos.Raw) (stackPos : String.Pos.Raw) (needlePos : String.Pos.Raw)
  | atEnd
deriving Inhabited

namespace ForwardSliceSearcher

partial def buildTable (pat : Slice) : Array String.Pos.Raw :=
  if pat.utf8ByteSize == 0 then
    #[]
  else
    let arr := Array.emptyWithCapacity pat.utf8ByteSize.byteIdx
    let arr := arr.push 0
    go ⟨1⟩ arr
where
  go (pos : String.Pos.Raw) (table : Array String.Pos.Raw) :=
    if h : pos < pat.utf8ByteSize then
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
    { internalState := .empty s.startPos }
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
      | .empty pos =>
        (∃ newPos, pos < newPos ∧ it'.internalState = .empty newPos) ∨
        it'.internalState = .atEnd
      | .proper needle table stackPos needlePos =>
        (∃ newStackPos newNeedlePos,
          stackPos < newStackPos ∧
          newStackPos ≤ s.utf8ByteSize ∧
          it'.internalState = .proper needle table newStackPos newNeedlePos) ∨
        it'.internalState = .atEnd
      | .atEnd => False
    | .skip _ => False
    | .done => True
  step := fun ⟨iter⟩ =>
    match iter with
    | .empty pos =>
      let res := .matched pos pos
      if h : pos ≠ s.endPos then
        pure ⟨.yield ⟨.empty (pos.next h)⟩ res, by simp⟩
      else
        pure ⟨.yield ⟨.atEnd⟩ res, by simp⟩
    | .proper needle table stackPos needlePos =>
      let rec findNext (startPos : String.Pos.Raw)
          (currStackPos : String.Pos.Raw) (needlePos : String.Pos.Raw) (h : stackPos ≤ currStackPos) :=
        if h1 : currStackPos < s.utf8ByteSize then
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
              simp only [pos_lt_eq, proper.injEq, true_and, exists_and_left, exists_eq', and_true,
                nextStackPos]
              constructor
              · simp [String.Pos.Raw.le_iff] at h haux ⊢
                omega
              · apply Pos.Raw.IsValidForSlice.le_utf8ByteSize
                apply Pos.isValidForSlice
            ⟨.yield ⟨.proper needle table nextStackPos needlePos⟩ res, hiter⟩
          else
            let needlePos := needlePos.inc
            if needlePos == needle.utf8ByteSize then
              let nextStackPos := currStackPos.inc
              let res := .matched (s.pos! startPos) (s.pos! nextStackPos)
              have hiter := by
                left
                exists nextStackPos
                simp only [pos_lt_eq, Pos.Raw.byteIdx_inc, proper.injEq, true_and, exists_and_left,
                  exists_eq', and_true, nextStackPos]
                constructor
                · simp [String.Pos.Raw.le_iff] at h ⊢
                  omega
                · simp [String.Pos.Raw.le_iff] at h1 ⊢
                  omega
              ⟨.yield ⟨.proper needle table nextStackPos 0⟩ res, hiter⟩
            else
              have hinv := by
                simp [String.Pos.Raw.le_iff] at h ⊢
                omega
              findNext startPos currStackPos.inc needlePos hinv
        else
          if startPos != s.utf8ByteSize then
            let res := .rejected (s.pos! startPos) (s.pos! currStackPos)
            ⟨.yield ⟨.atEnd⟩ res, by simp⟩
          else
            ⟨.done, by simp⟩
        termination_by s.utf8ByteSize.byteIdx - currStackPos.byteIdx
        decreasing_by
          simp at h1 ⊢
          omega

      findNext stackPos stackPos needlePos (by simp)
    | .atEnd => pure ⟨.done, by simp⟩

private def toPair : ForwardSliceSearcher s → (Nat × Nat)
  | .empty pos => (1, s.utf8ByteSize.byteIdx - pos.offset.byteIdx)
  | .proper _ _ sp _ => (1, s.utf8ByteSize.byteIdx - sp.byteIdx)
  | .atEnd => (0, 0)

private instance : WellFoundedRelation (ForwardSliceSearcher s) where
  rel s1 s2 := Prod.Lex (· < ·) (· < ·) s1.toPair s2.toPair
  wf := by
    apply InvImage.wf
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
      simp only [Std.Iterators.IterM.IsPlausibleStep, Std.Iterators.Iterator.IsPlausibleStep] at h'
      split at h'
      · next heq =>
        rw [heq]
        rcases h' with ⟨np, h1', h2'⟩ | h'
        · rw [h2']
          apply Prod.Lex.right'
          · simp
          · have haux := np.isValidForSlice.le_utf8ByteSize
            simp [Slice.Pos.lt_iff, String.Pos.Raw.le_iff] at h1' haux ⊢
            omega
        · apply Prod.Lex.left
          simp [h']
      · next heq =>
        rw [heq]
        rcases h' with ⟨np, sp, h1', h2', h3'⟩ | h'
        · rw [h3']
          apply Prod.Lex.right'
          · simp
          · simp [String.Pos.Raw.le_iff] at h1' h2' ⊢
            omega
        · apply Prod.Lex.left
          simp [h']
      · contradiction
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
    Internal.memcmp s pat s.startPos.offset pat.startPos.offset pat.utf8ByteSize hs hp
  else
    false

@[inline]
def dropPrefix? (s : Slice) (pat : Slice) : Option Slice :=
  if startsWith s pat then
    some <| s.replaceStart <| s.pos! <| s.startPos.offset + pat.utf8ByteSize
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
    let sStart := s.endPos.offset - pat.utf8ByteSize
    let patStart := pat.startPos.offset
    have hs := by
      simp [sStart, Pos.Raw.le_iff] at h ⊢
      omega
    have hp := by
      simp [patStart, Pos.Raw.le_iff] at h ⊢
    Internal.memcmp s pat sStart patStart pat.utf8ByteSize hs hp
  else
    false

@[inline]
def dropSuffix? (s : Slice) (pat : Slice) : Option Slice :=
  if endsWith s pat then
    some <| s.replaceEnd <| s.pos! <| s.endPos.offset - pat.utf8ByteSize
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
