/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving, Markus Himmel
-/
module

prelude
public import Init.Data.String.Basic
public import Init.Data.Iterators.Combinators.FilterMap
public import Init.Data.Iterators.Consumers.Loop
import Init.Omega
import Init.Data.Iterators.Consumers.Collect

set_option doc.verso true

public section

namespace String.Slice

structure PosIterator (s : Slice) where
  currPos : s.Pos
deriving Inhabited

set_option doc.verso false
/--
Creates an iterator over all valid positions within {name}`s`.

Examples
 * {lean}`("abc".toSlice.positions.map (fun ⟨p, h⟩ => p.get h) |>.toList) = ['a', 'b', 'c']`
 * {lean}`("abc".toSlice.positions.map (·.val.offset.byteIdx) |>.toList) = [0, 1, 2]`
 * {lean}`("ab∀c".toSlice.positions.map (fun ⟨p, h⟩ => p.get h) |>.toList) = ['a', 'b', '∀', 'c']`
 * {lean}`("ab∀c".toSlice.positions.map (·.val.offset.byteIdx) |>.toList) = [0, 1, 2, 5]`
-/
def positions (s : Slice) : Std.Iter (α := PosIterator s) { p : s.Pos // p ≠ s.endPos } :=
  { internalState := { currPos := s.startPos }}

set_option doc.verso true

namespace PosIterator

instance [Pure m] :
    Std.Iterator (PosIterator s) m { p : s.Pos // p ≠ s.endPos } where
  IsPlausibleStep it
    | .yield it' out =>
      ∃ h : it.internalState.currPos ≠ s.endPos,
        it'.internalState.currPos = it.internalState.currPos.next h ∧
        it.internalState.currPos = out
    | .skip _ => False
    | .done => it.internalState.currPos = s.endPos
  step := fun ⟨⟨currPos⟩⟩ =>
    if h : currPos = s.endPos then
      pure (.deflate ⟨.done, by simp [h]⟩)
    else
      pure (.deflate ⟨.yield ⟨⟨currPos.next h⟩⟩ ⟨currPos, h⟩, by simp [h]⟩)

private def finitenessRelation [Pure m] :
    Std.Iterators.FinitenessRelation (PosIterator s) m where
  Rel := InvImage WellFoundedRelation.rel
      (fun it => s.utf8ByteSize - it.internalState.currPos.offset.byteIdx)
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by
    simp_wf
    obtain ⟨step, h, h'⟩ := h
    cases step
    · cases h
      obtain ⟨h1, h2, _⟩ := h'
      have h3 := Char.utf8Size_pos (it.internalState.currPos.get h1)
      have h4 := it.internalState.currPos.isValidForSlice.le_utf8ByteSize
      simp [Pos.ext_iff, String.Pos.Raw.ext_iff] at h1 h2 h4
      omega
    · cases h'
    · cases h

@[no_expose]
instance [Pure m] : Std.Iterators.Finite (PosIterator s) m :=
  .of_finitenessRelation finitenessRelation

instance [Monad m] [Monad n] : Std.IteratorLoop (PosIterator s) m n :=
  .defaultImplementation

docs_to_verso positions

end PosIterator

/--
Creates an iterator over all characters (Unicode code points) in {name}`s`.

Examples:
 * {lean}`"abc".toSlice.chars.toList = ['a', 'b', 'c']`
 * {lean}`"ab∀c".toSlice.chars.toList = ['a', 'b', '∀', 'c']`
-/
@[expose, inline]
def chars (s : Slice) :=
  Std.Iter.map (fun ⟨pos, h⟩ => pos.get h) (positions s)

@[deprecated "There is no constant-time length function on slices. Use `s.positions.length` instead, or `isEmpty` if you only need to know whether the slice is empty." (since := "2025-11-20")]
def length (s : Slice) : Nat :=
  s.positions.length

structure RevPosIterator (s : Slice) where
  currPos : s.Pos
deriving Inhabited

set_option doc.verso false
/--
Creates an iterator over all valid positions within {name}`s`, starting from the last valid
position and iterating towards the first one.

Examples
 * {lean}`("abc".toSlice.revPositions.map (fun ⟨p, h⟩ => p.get h) |>.toList) = ['c', 'b', 'a']`
 * {lean}`("abc".toSlice.revPositions.map (·.val.offset.byteIdx) |>.toList) = [2, 1, 0]`
 * {lean}`("ab∀c".toSlice.revPositions.map (fun ⟨p, h⟩ => p.get h) |>.toList) = ['c', '∀', 'b', 'a']`
 * {lean}`("ab∀c".toSlice.revPositions.map (·.val.offset.byteIdx) |>.toList) = [5, 2, 1, 0]`
-/
def revPositions (s : Slice) : Std.Iter (α := RevPosIterator s) { p : s.Pos // p ≠ s.endPos } :=
  { internalState := { currPos := s.endPos }}

set_option doc.verso true

namespace RevPosIterator

instance [Pure m] :
    Std.Iterator (RevPosIterator s) m { p : s.Pos // p ≠ s.endPos } where
  IsPlausibleStep it
    | .yield it' out =>
      ∃ h : it.internalState.currPos ≠ s.startPos,
        it'.internalState.currPos = it.internalState.currPos.prev h ∧
        it.internalState.currPos.prev h = out
    | .skip _ => False
    | .done => it.internalState.currPos = s.startPos
  step := fun ⟨⟨currPos⟩⟩ =>
    if h : currPos = s.startPos then
      pure (.deflate ⟨.done, by simp [h]⟩)
    else
      let prevPos := currPos.prev h
      pure (.deflate ⟨.yield ⟨⟨prevPos⟩⟩ ⟨prevPos, Pos.prev_ne_endPos⟩, by simp [h, prevPos]⟩)

private def finitenessRelation [Pure m] :
    Std.Iterators.FinitenessRelation (RevPosIterator s) m where
  Rel := InvImage WellFoundedRelation.rel
      (fun it => it.internalState.currPos.offset.byteIdx)
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by
    simp_wf
    obtain ⟨step, h, h'⟩ := h
    cases step
    · cases h
      obtain ⟨h1, h2, _⟩ := h'
      have h3 := Pos.offset_prev_lt_offset (h := h1)
      simp [Pos.ext_iff, String.Pos.Raw.ext_iff, String.Pos.Raw.lt_iff] at h2 h3
      omega
    · cases h'
    · cases h

@[no_expose]
instance [Pure m] : Std.Iterators.Finite (RevPosIterator s) m :=
  .of_finitenessRelation finitenessRelation

instance [Monad m] [Monad n] : Std.IteratorLoop (RevPosIterator s) m n :=
  .defaultImplementation

docs_to_verso revPositions

end RevPosIterator

/--
Creates an iterator over all characters (Unicode code points) in {name}`s`, starting from the end
of the slice and iterating towards the start.

Example:
 * {lean}`"abc".toSlice.revChars.toList = ['c', 'b', 'a']`
 * {lean}`"ab∀c".toSlice.revChars.toList = ['c', '∀', 'b', 'a']`
-/
@[expose, inline]
def revChars (s : Slice) :=
  Std.Iter.map (fun ⟨pos, h⟩ => pos.get h) (revPositions s)

structure ByteIterator where
  s : Slice
  offset : String.Pos.Raw
deriving Inhabited

set_option doc.verso false
/--
Creates an iterator over all bytes in {name}`s`.

Examples:
 * {lean}`"abc".toSlice.bytes.toList = [97, 98, 99]`
 * {lean}`"ab∀c".toSlice.bytes.toList = [97, 98, 226, 136, 128, 99]`
-/
def bytes (s : Slice) : Std.Iter (α := ByteIterator) UInt8 :=
  { internalState := { s, offset := s.startPos.offset }}

set_option doc.verso true

namespace ByteIterator

instance [Pure m] : Std.Iterator ByteIterator m UInt8 where
  IsPlausibleStep it
    | .yield it' out =>
      ∃ h1 : it.internalState.offset < it.internalState.s.rawEndPos,
        it.internalState.s = it'.internalState.s ∧
        it'.internalState.offset = it.internalState.offset.inc ∧
        it.internalState.s.getUTF8Byte it.internalState.offset h1 = out
    | .skip _ => False
    | .done => ¬ it.internalState.offset < it.internalState.s.rawEndPos
  step := fun ⟨s, offset⟩ =>
    if h : offset < s.rawEndPos then
      pure (.deflate ⟨.yield ⟨s, offset.inc⟩ (s.getUTF8Byte offset h), by simp [h]⟩)
    else
      pure (.deflate ⟨.done, by simp [h]⟩)

private def finitenessRelation [Pure m] :
    Std.Iterators.FinitenessRelation (ByteIterator) m where
  Rel := InvImage WellFoundedRelation.rel
      (fun it => it.internalState.s.utf8ByteSize - it.internalState.offset.byteIdx)
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by
    simp_wf
    obtain ⟨step, h, h'⟩ := h
    cases step
    · cases h
      obtain ⟨h1, h2, h3, h4⟩ := h'
      clear h4
      generalize it'.internalState.s = s at *
      cases h2
      simp [String.Pos.Raw.ext_iff, String.Pos.Raw.lt_iff] at h1 h3
      omega
    · cases h'
    · cases h

@[no_expose]
instance [Pure m] : Std.Iterators.Finite ByteIterator m :=
  .of_finitenessRelation finitenessRelation

instance [Monad m] [Monad n] : Std.IteratorLoop ByteIterator m n :=
  .defaultImplementation

docs_to_verso bytes

end ByteIterator

structure RevByteIterator where
  s : Slice
  offset : String.Pos.Raw
  hinv : offset ≤ s.rawEndPos

set_option doc.verso false
/--
Creates an iterator over all bytes in {name}`s`, starting from the last one and iterating towards
the first one.

Examples:
 * {lean}`"abc".toSlice.revBytes.toList = [99, 98, 97]`
 * {lean}`"ab∀c".toSlice.revBytes.toList = [99, 128, 136, 226, 98, 97]`
-/
def revBytes (s : Slice) : Std.Iter (α := RevByteIterator) UInt8 :=
  { internalState := { s, offset := s.endPos.offset, hinv := by simp }}

set_option doc.verso true

instance : Inhabited RevByteIterator where
  default :=
    let s := default
    { s := s, offset := s.endPos.offset, hinv := by simp}

namespace RevByteIterator

instance [Pure m] : Std.Iterator RevByteIterator m UInt8 where
  IsPlausibleStep it
    | .yield it' out =>
      ∃ h1 : it.internalState.offset.dec < it.internalState.s.rawEndPos,
        it.internalState.s = it'.internalState.s ∧
        it.internalState.offset ≠ 0 ∧
        it'.internalState.offset = it.internalState.offset.dec ∧
        it.internalState.s.getUTF8Byte it.internalState.offset.dec h1 = out
    | .skip _ => False
    | .done => it.internalState.offset = 0
  step := fun ⟨s, offset, hinv⟩ =>
    if h : offset ≠ 0 then
      let nextOffset := offset.dec
      have hbound := by
        simp [String.Pos.Raw.le_iff, nextOffset, String.Pos.Raw.lt_iff] at h hinv ⊢
        omega
      have hinv := by
        simp [String.Pos.Raw.le_iff, nextOffset] at hinv ⊢
        omega
      have hiter := by simp [nextOffset, hbound, h]
      pure (.deflate ⟨.yield ⟨s, nextOffset, hinv⟩ (s.getUTF8Byte nextOffset hbound), hiter⟩)
    else
      pure (.deflate ⟨.done, by simpa using h⟩)

private def finitenessRelation [Pure m] :
    Std.Iterators.FinitenessRelation (RevByteIterator) m where
  Rel := InvImage WellFoundedRelation.rel
      (fun it => it.internalState.offset.byteIdx)
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by
    simp_wf
    obtain ⟨step, h, h'⟩ := h
    cases step
    · cases h
      obtain ⟨h1, h2, h3, h4, h5⟩ := h'
      rw [h4]
      simp at h1 h3 ⊢
      omega
    · cases h'
    · cases h

@[no_expose]
instance [Pure m] : Std.Iterators.Finite RevByteIterator m :=
  .of_finitenessRelation finitenessRelation

instance [Monad m] [Monad n] : Std.IteratorLoop RevByteIterator m n :=
  .defaultImplementation

docs_to_verso revBytes

instance : ForIn Id String.Slice Char where
  forIn s b f := ForIn.forIn s.chars b f

end RevByteIterator

/--
Folds a function over a slice from the start, accumulating a value starting with {name}`init`. The
accumulated value is combined with each character in order, using {name}`f`.

Examples:
 * {lean}`"coffee tea water".toSlice.foldl (fun n c => if c.isWhitespace then n + 1 else n) 0 = 2`
 * {lean}`"coffee tea and water".toSlice.foldl (fun n c => if c.isWhitespace then n + 1 else n) 0 = 3`
 * {lean}`"coffee tea water".toSlice.foldl (·.push ·) "" = "coffee tea water"`
-/
@[inline]
def foldl {α : Type u} (f : α → Char → α) (init : α) (s : Slice) : α :=
  Std.Iter.fold f init (chars s)

/--
Folds a function over a slice from the end, accumulating a value starting with {name}`init`. The
accumulated value is combined with each character in reverse order, using {name}`f`.

Examples:
 * {lean}`"coffee tea water".toSlice.foldr (fun c n => if c.isWhitespace then n + 1 else n) 0 = 2`
 * {lean}`"coffee tea and water".toSlice.foldr (fun c n => if c.isWhitespace then n + 1 else n) 0 = 3`
 * {lean}`"coffee tea water".toSlice.foldr (fun c s => s.push c) "" = "retaw aet eeffoc"`
-/
@[inline]
def foldr {α : Type u} (f : Char → α → α) (init : α) (s : Slice) : α :=
  Std.Iter.fold (flip f) init (revChars s)

end Slice

@[inline]
def Internal.toSliceWithProof {s : String} :
    { p : s.toSlice.Pos // p ≠ s.toSlice.endPos } → { p : s.Pos // p ≠ s.endPos } :=
  fun ⟨p, h⟩ => ⟨Pos.ofToSlice p, by simpa [← Pos.toSlice_inj]⟩

/--
Creates an iterator over all valid positions within {name}`s`.

Examples
 * {lean}`("abc".positions.map (fun ⟨p, h⟩ => p.get h) |>.toList) = ['a', 'b', 'c']`
 * {lean}`("abc".positions.map (·.val.offset.byteIdx) |>.toList) = [0, 1, 2]`
 * {lean}`("ab∀c".positions.map (fun ⟨p, h⟩ => p.get h) |>.toList) = ['a', 'b', '∀', 'c']`
 * {lean}`("ab∀c".positions.map (·.val.offset.byteIdx) |>.toList) = [0, 1, 2, 5]`
-/
@[inline]
def positions (s : String) :=
  (s.toSlice.positions.map Internal.toSliceWithProof : Std.Iter { p : s.Pos // p ≠ s.endPos })

/--
Creates an iterator over all characters (Unicode code points) in {name}`s`.

Examples:
 * {lean}`"abc".chars.toList = ['a', 'b', 'c']`
 * {lean}`"ab∀c".chars.toList = ['a', 'b', '∀', 'c']`
-/
@[inline]
def chars (s : String) :=
  (s.toSlice.chars : Std.Iter Char)

/--
Creates an iterator over all valid positions within {name}`s`, starting from the last valid
position and iterating towards the first one.

Examples
 * {lean}`("abc".revPositions.map (fun ⟨p, h⟩ => p.get h) |>.toList) = ['c', 'b', 'a']`
 * {lean}`("abc".revPositions.map (·.val.offset.byteIdx) |>.toList) = [2, 1, 0]`
 * {lean}`("ab∀c".revPositions.map (fun ⟨p, h⟩ => p.get h) |>.toList) = ['c', '∀', 'b', 'a']`
 * {lean}`("ab∀c".toSlice.revPositions.map (·.val.offset.byteIdx) |>.toList) = [5, 2, 1, 0]`
-/
@[inline]
def revPositions (s : String) :=
  (s.toSlice.revPositions.map Internal.toSliceWithProof : Std.Iter { p : s.Pos // p ≠ s.endPos })

/--
Creates an iterator over all characters (Unicode code points) in {name}`s`, starting from the end
of the slice and iterating towards the start.

Example:
 * {lean}`"abc".revChars.toList = ['c', 'b', 'a']`
 * {lean}`"ab∀c".revChars.toList = ['c', '∀', 'b', 'a']`
-/
@[inline]
def revChars (s : String) :=
  (s.toSlice.revChars : Std.Iter Char)

/--
Creates an iterator over all bytes in {name}`s`.

Examples:
 * {lean}`"abc".byteIterator.toList = [97, 98, 99]`
 * {lean}`"ab∀c".byteIterator.toList = [97, 98, 226, 136, 128, 99]`
-/
@[inline]
def byteIterator (s : String) :=
  (s.toSlice.bytes : Std.Iter UInt8)

/--
Creates an iterator over all bytes in {name}`s`, starting from the last one and iterating towards
the first one.

Examples:
 * {lean}`"abc".revBytes.toList = [99, 98, 97]`
 * {lean}`"ab∀c".revBytes.toList = [99, 128, 136, 226, 98, 97]`
-/
@[inline]
def revBytes (s : String) :=
  (s.toSlice.revBytes : Std.Iter UInt8)

instance : ForIn Id String Char where
  forIn s b f := ForIn.forIn s.toSlice b f

end String
