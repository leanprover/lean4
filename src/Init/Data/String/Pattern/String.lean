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

public section

namespace String.Slice.Pattern

inductive ForwardSliceSearcher (s : Slice) where
  | empty (pos : s.Pos)
  | proper (needle : Slice) (table : Array String.Pos) (stackPos : String.Pos) (needlePos : String.Pos)
  | atEnd
  deriving Inhabited

namespace ForwardSliceSearcher

def buildTable (pat : Slice) : Array String.Pos :=
  if pat.utf8ByteSize == 0 then
    #[]
  else
    let arr := Array.emptyWithCapacity pat.utf8ByteSize.byteIdx
    let arr := arr.push 0
    go ⟨1⟩ arr
where
  go (pos : String.Pos) (table : Array String.Pos) :=
    if h : pos < pat.utf8ByteSize then
      let patByte := pat.getUtf8Byte pos h
      let distance := computeDistance table[table.size - 1]! patByte table
      let distance := if patByte = pat.getUtf8Byte distance sorry then distance.inc else distance
      go pos.inc (table.push distance)
    else
      table
  termination_by pat.utf8ByteSize.byteIdx - pos.byteIdx
  decreasing_by
    simp at h ⊢
    omega

  computeDistance (distance : String.Pos) (patByte : UInt8) (table : Array String.Pos) : String.Pos :=
    if distance > 0 && patByte != pat.getUtf8Byte distance sorry then
      computeDistance table[distance.byteIdx - 1]! patByte table
    else
      distance
  termination_by distance
  decreasing_by sorry

@[inline]
def iter (s : Slice) (pat : Slice) : Std.Iter (α := ForwardSliceSearcher s) (SearchStep s) :=
  if pat.utf8ByteSize == 0 then
    { internalState := .empty s.startPos }
  else
    { internalState := .proper pat (buildTable pat) s.startPos.offset pat.startPos.offset }

instance (s : Slice) : Std.Iterators.Iterator (ForwardSliceSearcher s) Id (SearchStep s) where
  IsPlausibleStep := sorry
  step := fun ⟨iter⟩ =>
    match iter with
    | .empty pos =>
      let res := .matched pos pos
      if h : pos ≠ s.endPos then
        pure ⟨.yield ⟨.empty (pos.next h)⟩ res, sorry⟩
      else
        pure ⟨.yield ⟨.atEnd⟩ res, sorry⟩
    | .proper needle table stackPos needlePos =>
      let rec backtrackIfNecessary (pat : Slice) (table : Array String.Pos) (stackByte : UInt8)
          (needlePos : String.Pos) : String.Pos :=
        if needlePos != 0 && stackByte != pat.getUtf8Byte needlePos sorry then
          backtrackIfNecessary pat table stackByte table[needlePos.byteIdx - 1]!
        else
          needlePos
      termination_by needlePos
      decreasing_by sorry

      let rec findNext (startPos : String.Pos) (pat : Slice) (table : Array String.Pos)
          (stackPos : String.Pos) (needlePos : String.Pos) :=
        if h1 : stackPos < s.utf8ByteSize then
          let stackByte := s.getUtf8Byte stackPos h1
          let needlePos := backtrackIfNecessary pat table stackByte needlePos
          let patByte := pat.getUtf8Byte needlePos sorry
          if stackByte != patByte then
            let nextStackPos := s.findNextPos stackPos h1 |>.offset
            let res := .rejected (s.pos! startPos) (s.pos! nextStackPos)
            ⟨.yield ⟨.proper pat table nextStackPos needlePos⟩ res, sorry⟩
          else
            let needlePos := needlePos.inc
            if needlePos == pat.utf8ByteSize then
              let nextStackPos := stackPos.inc
              let res := .matched (s.pos! startPos) (s.pos! nextStackPos)
              ⟨.yield ⟨.proper pat table nextStackPos 0⟩ res, sorry⟩
            else
              findNext startPos pat table stackPos.inc needlePos
        else
          if startPos != s.utf8ByteSize then
            let res := .rejected (s.pos! startPos) (s.pos! stackPos)
            ⟨.yield ⟨.atEnd⟩ res, sorry⟩
          else
            ⟨.done, sorry⟩
        termination_by s.utf8ByteSize - stackPos
        decreasing_by sorry
      findNext stackPos needle table stackPos needlePos
    | .atEnd => pure ⟨.done, sorry⟩

def finitenessRelation : Std.Iterators.FinitenessRelation (ForwardSliceSearcher s) Id where
  rel := sorry
  wf := sorry
  subrelation := sorry

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
      simp [Pos.le_iff] at h ⊢
      omega
    have hp := by
      simp [Pos.le_iff]
    Internal.memcmp s pat s.startPos.offset pat.startPos.offset pat.utf8ByteSize hs hp
  else
    false

@[inline]
def dropPrefix? (s : Slice) (pat : Slice) : Option Slice :=
  if startsWith s pat then
    /-
    SAFETY: This pos! works because `s` has the prefix `pat` starting from the initial value of
    `sCurr` so `sCurr` is at the end of the `pat` prefix in `s` and thus at a valid unicode offset
    right now
    -/
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

/-

h : pend ≤ send - sstart + pstart

⊢ sstart + (pend - pstart) ≤ send - sstart
-/

@[inline]
def endsWith (s : Slice) (pat : Slice) : Bool :=
  if h : pat.utf8ByteSize ≤ s.utf8ByteSize then
    -- SAFETY: these are true by simple arithmetic with h
    let sStart := s.endPos.offset - pat.utf8ByteSize
    let patStart := pat.startPos.offset
    have hs := by
      simp [Pos.le_iff] at h ⊢
      sorry
    have hp := by
      simp [Pos.le_iff] at h ⊢
      sorry
    Internal.memcmp s pat sStart patStart pat.utf8ByteSize hs hp
  else
    false

@[inline]
def dropSuffix? (s : Slice) (pat : Slice) : Option Slice :=
  if endsWith s pat then
    -- SAFETY: Same as dropPrefix?
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
