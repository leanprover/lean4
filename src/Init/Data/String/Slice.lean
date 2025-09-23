/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Init.Data.String.Pattern
public import Init.Data.Iterators.Consumers.Monadic.Collect
public import Init.Data.Ord.Basic
import Init.Data.Iterators.Combinators.FilterMap

/-!
This module defines the programming API for `String.Slice`. The API mostly consists of functionality
for searching for various kinds of pattern matches in slices to iterate over them, provide subslices
according to matches etc. The key design principles behind this module are:
- Instead of providing one function per kind of pattern the API is generic over various kinds of
  patterns. Thus it only provides e.g. one kind of function for looking for the position of the
  first occurence of a pattern (`String.Slice.find?`). Currently the supported patterns are:
  - `Char`
  - `Char → Bool`
  - `String` and `String.Slice`
- Whenever a slice gets mutated a new slice is returned to allow for repeated chaining of functions
  with minimal allocations. If necessary the slice can ultimately be converted back to `String`
  using `String.Slice.copy`
- Instead of allocating intermediate collections the operations that iterate over slices in various
  ways (characters, positions etc.) return iterators that can be collected into other collections if
  necessary.
- When sensible the API provides functionality for searching both in a forward and backward manner,
  e.g. `String.Slice.find?` and `String.Slice.revFind?`
-/

public section

namespace String.Slice

open Pattern

/--
Checks whether a slice is empty.

Empty slices have `utf8ByteSize` `0`.

Examples:
 * `"".toSlice.isEmpty = true`
 * `" ".toSlice.isEmpty = false`
 * `(" ".toSlice.drop 1).isEmpty = true`
-/
@[inline]
def isEmpty (s : Slice) : Bool := s.utf8ByteSize == 0

section ForwardPatternUsers

variable {ρ : Type} {σ : Slice → Type}
variable [∀ s, Std.Iterators.Iterator (σ s) Id (SearchStep s)]
variable [∀ s, Std.Iterators.Finite (σ s) Id]
variable [∀ s, Std.Iterators.IteratorLoop (σ s) Id Id]

/--
Checks whether the slice (`s`) begins with the pattern (`pat`).

This function is generic over all currently supported patterns.

Examples:
 * `"red green blue".toSlice.startsWith "red" = true`
 * `"red green blue".toSlice.startsWith "green" = false`
 * `"red green blue".toSlice.startsWith "" = true`
 * `"red green blue".toSlice.startsWith 'r' = true`
 * `"red green blue".toSlice.startsWith Char.isLower = true`
-/
@[inline]
def startsWith [ForwardPattern ρ] (s : Slice) (pat : ρ) : Bool :=
  ForwardPattern.startsWith s pat

inductive SplitIterator (ρ : Type) [ToForwardSearcher ρ σ] where
  | operating (s : Slice) (currPos : s.Pos) (searcher : Std.Iter (α := σ s) (SearchStep s))
  | atEnd
  deriving Inhabited

namespace SplitIterator

variable [ToForwardSearcher ρ σ]

instance [Pure m] : Std.Iterators.Iterator (SplitIterator ρ) m Slice where
  IsPlausibleStep := fun _ _ => True
  step := fun ⟨iter⟩ =>
    match iter with
    | .operating s currPos searcher =>
      match Internal.nextMatch searcher with
      | some (searcher, startPos, endPos) =>
        let slice := s.replaceStartEnd! currPos startPos
        let nextIt := ⟨.operating s endPos searcher⟩
        pure ⟨.yield nextIt slice, by simp⟩
      | none =>
        let slice := s.replaceStart currPos
        pure ⟨.yield ⟨.atEnd⟩ slice, by simp⟩
    | .atEnd => pure ⟨.done, by simp⟩

-- TODO: Finiteness after we have a notion of lawful searcher

instance [Monad m] [Monad n] : Std.Iterators.IteratorCollect (SplitIterator ρ) m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorCollectPartial (SplitIterator ρ) m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorLoop (SplitIterator ρ) m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorLoopPartial (SplitIterator ρ) m n :=
  .defaultImplementation

end SplitIterator

/--
Splits a slice at each subslice that matches the pattern `pat`.

The subslices that matched the pattern are not included in any of the resulting subslices. If
multiple subslices in a row match the pattern, the resulting list will contain empty strings.

This function is generic over all currently supported patterns.

Examples:
 * `("coffee tea water".toSlice.split Char.isWhitespace).allowNontermination.toList == ["coffee".toSlice, "tea".toSlice, "water".toSlice]`
 * `("coffee tea water".toSlice.split ' ').allowNontermination.toList == ["coffee".toSlice, "tea".toSlice, "water".toSlice]`
 * `("coffee tea water".toSlice.split " tea ").allowNontermination.toList == ["coffee".toSlice, "water".toSlice]`
-/
@[specialize pat]
def split [ToForwardSearcher ρ σ] (s : Slice) (pat : ρ) : Std.Iter (α := SplitIterator ρ) Slice :=
  { internalState := .operating s s.startPos (ToForwardSearcher.toSearcher s pat) }

inductive SplitInclusiveIterator (ρ : Type) [ToForwardSearcher ρ σ] where
  | operating (s : Slice) (currPos : s.Pos) (searcher : Std.Iter (α := σ s) (SearchStep s))
  | atEnd
  deriving Inhabited

namespace SplitInclusiveIterator

variable [ToForwardSearcher ρ σ]

instance [Pure m] : Std.Iterators.Iterator (SplitInclusiveIterator ρ) m Slice where
  IsPlausibleStep := fun _ _ => True
  step := fun ⟨iter⟩ =>
    match iter with
    | .operating s currPos searcher =>
      match Internal.nextMatch searcher with
      | some (searcher, _, endPos) =>
        let slice := s.replaceStartEnd! currPos endPos
        let nextIt := ⟨.operating s endPos searcher⟩
        pure ⟨.yield nextIt slice, by simp⟩
      | none =>
        if currPos != s.endPos then
          let slice := s.replaceStart currPos
          pure ⟨.yield ⟨.atEnd⟩ slice, by simp⟩
        else
          pure ⟨.done, by simp⟩
    | .atEnd => pure ⟨.done, by simp⟩

-- TODO: Finiteness after we have a notion of lawful searcher

instance [Monad m] [Monad n] :
    Std.Iterators.IteratorCollect (SplitInclusiveIterator ρ) m n :=
  .defaultImplementation

instance [Monad m] [Monad n] :
    Std.Iterators.IteratorCollectPartial (SplitInclusiveIterator ρ) m n :=
  .defaultImplementation

instance [Monad m] [Monad n] :
    Std.Iterators.IteratorLoop (SplitInclusiveIterator ρ) m n :=
  .defaultImplementation

instance [Monad m] [Monad n] :
    Std.Iterators.IteratorLoopPartial (SplitInclusiveIterator ρ) m n :=
  .defaultImplementation

end SplitInclusiveIterator

/--
Splits a slice at each subslice that matches the pattern `pat`. Unlike `split` the matched subslices
are included at the end of each subslice.

This function is generic over all currently supported patterns.

Examples:
 * `("coffee tea water".toSlice.splitInclusive Char.isWhitespace).allowNontermination.toList == ["coffee ".toSlice, "tea ".toSlice, "water".toSlice]`
 * `("coffee tea water".toSlice.splitInclusive ' ').allowNontermination.toList == ["coffee ".toSlice, "tea ".toSlice, "water".toSlice]`
 * `("coffee tea water".toSlice.splitInclusive " tea ").allowNontermination.toList == ["coffee tea ".toSlice, "water".toSlice]`
-/
@[specialize pat]
def splitInclusive [ToForwardSearcher ρ σ] (s : Slice) (pat : ρ) :
    Std.Iter (α := SplitInclusiveIterator ρ) Slice :=
  { internalState := .operating s s.startPos (ToForwardSearcher.toSearcher s pat) }

/--
Removes the specified number of characters (Unicode code points) from the start of the slice.

If `n` is greater than the amount of characters in `s`, returns an empty slice.

Examples:
 * `"red green blue".toSlice.drop 4 == "green blue".toSlice`
 * `"red green blue".toSlice.drop 10 == "blue".toSlice`
 * `"red green blue".toSlice.drop 50 == "".toSlice`
-/
@[inline]
def drop (s : Slice) (n : Nat) : Slice :=
  s.replaceStart (s.startPos.nextn n)

/--
Creates a new string by removing the longest prefix from `s` in which `p` returns `true` for all
characters.

Examples:
 * `"red green blue".toSlice.dropWhile Char.isLower == " green blue".toSlice`
 * `"red green blue".toSlice.dropWhile 'r' == "ed green blue".toSlice`
 * `"red red green blue".toSlice.dropWhile "red " == "green blue".toSlice`
 * `"red green blue".toSlice.dropWhile (fun (_ : Char) => true) == "".toSlice`
-/
@[specialize pat]
def dropWhile [ToForwardSearcher ρ σ] (s : Slice) (pat : ρ) : Slice :=
  let searcher := ToForwardSearcher.toSearcher s pat
  match Internal.nextReject searcher with
  | some (_, startPos, _) => s.replaceStart startPos
  | none => s.replaceStart s.endPos

/--
Removes leading whitespace from a slice by moving its start position to the first non-whitespace
character, or to its end position if there is no non-whitespace character.

“Whitespace” is defined as characters for which `Char.isWhitespace` returns `true`.
-/
@[inline]
def trimAsciiStart (s : Slice) : Slice :=
  -- If we want to optimize this can be pushed further by specialising for ASCII
  dropWhile s Char.isWhitespace

/--
Creates a new slice that contains the first `n` characters (Unicode code points) of `s`.

If `n` is greater than `s.length`, returns `s`.

Examples:
 * `"red green blue".toSlice.take 3 == "red".toSlice`
 * `"red green blue".toSlice.take 1 == "r".toSlice`
 * `"red green blue".toSlice.take 0 == "".toSlice`
 * `"red green blue".toSlice.take 100 == "red green blue".toSlice`
-/
@[inline]
def take (s : Slice) (n : Nat) : Slice :=
  s.replaceEnd (s.startPos.nextn n)

/--
Creates a new slice that contains the longest prefix of `s` for which `pat` matched
(potentially repeatedly).

This function is generic over all currently supported patterns.

Examples:
 * `"red green blue".toSlice.takeWhile Char.isLower == "red".toSlice`
 * `"red green blue".toSlice.takeWhile 'r' == "r".toSlice`
 * `"red red green blue".toSlice.takeWhile "red " == "red red ".toSlice`
 * `"red green blue".toSlice.takeWhile (fun (_ : Char) => true) == "red green blue".toSlice`
-/
@[specialize pat]
def takeWhile [ToForwardSearcher ρ σ] (s : Slice) (pat : ρ) : Slice :=
  let searcher := ToForwardSearcher.toSearcher s pat
  match Internal.nextReject searcher with
  | some (_, startPos, _) => s.replaceEnd startPos
  | none => s

/--
If `pat` matches a prefix of `s`, returns the remainder. Returns `none` otherwise.

Use `String.Slice.dropPrefix` to return the string unchanged when `pat` does not match a prefix.

This function is generic over all currently supported patterns.

Examples:
 * `"red green blue".toSlice.dropPrefix? "red " == some "green blue".toSlice`
 * `"red green blue".toSlice.dropPrefix? "reed " == none`
 * `"red green blue".toSlice.dropPrefix? 'r' == some "ed green blue".toSlice`
 * `"red green blue".toSlice.dropPrefix? Char.isLower == some "ed green blue".toSlice`
-/
@[inline]
def dropPrefix? [ForwardPattern ρ] (s : Slice) (pat : ρ) : Option Slice :=
  ForwardPattern.dropPrefix? s pat

/--
If `pat` matches a prefix of `s`, returns the remainder. Returns `s` unmodified otherwise.

Use `String.Slice.dropPrefix?` to return `none` when `pat` does not match a prefix.

This function is generic over all currently supported patterns.

Examples:
 * `"red green blue".toSlice.dropPrefix "red " == some "green blue".toSlice`
 * `"red green blue".toSlice.dropPrefix "reed " == "red green blue".toSlice`
 * `"red green blue".toSlice.dropPrefix 'r' == some "ed green blue".toSlice`
 * `"red green blue".toSlice.dropPrefix Char.isLower == some "ed green blue".toSlice`
-/
@[specialize pat]
def dropPrefix [ForwardPattern ρ] (s : Slice) (pat : ρ) : Slice :=
  dropPrefix? s pat |>.getD s

/--
Finds the position of the first match of the pattern `pat` in a slice `true`. If there is no match
`none` is returned.

This function is generic over all currently supported patterns.

Examples:
 * `("coffee tea water".toSlice.find? Char.isWhitespace).map (·.get!) == some ' '`
 * `"tea".toSlice.find? (fun (c : Char) => c == 'X') == none`
 * `("coffee tea water".toSlice.find? "tea").map (·.get!) == some 't'`
-/
@[specialize pat]
def find? [ToForwardSearcher ρ σ] (s : Slice) (pat : ρ) : Option s.Pos :=
  let searcher := ToForwardSearcher.toSearcher s pat
  match Internal.nextMatch searcher with
  | some (_, startPos, _) => some startPos
  | none => none

/--
Checks whether a slice has a match of the pattern `pat` anywhere.

This function is generic over all currently supported patterns.

Examples:
 * `"coffee tea water".toSlice.contains Char.isWhitespace == true`
 * `"tea".toSlice.contains (fun (c : Char) => c == 'X') == false`
 * `"coffee tea water".toSlice.contains "tea" == true`
-/
@[specialize pat]
def contains [ToForwardSearcher ρ σ] (s : Slice) (pat : ρ) : Bool :=
  let searcher := ToForwardSearcher.toSearcher s pat
  Internal.nextMatch searcher |>.isSome

/--
Checks whether a slice only consists of matches of the pattern `pat` anywhere.

Short-circuits at the first pattern mis-match.

This function is generic over all currently supported patterns.

Examples:
 * `"brown".toSlice.all Char.isLower == true`
 * `"brown and orange".toSlice.all Char.isLower == false`
 * `"aaaaaa".toSlice.all 'a' == true`
 * `"aaaaaa".toSlice.all "aa" == true`
-/
@[specialize pat]
def all [ToForwardSearcher ρ σ] (s : Slice) (pat : ρ) : Bool :=
  let searcher := ToForwardSearcher.toSearcher s pat
  Internal.nextReject searcher |>.isNone

end ForwardPatternUsers

section BackwardPatternUsers

variable {σ : Slice → Type}
variable [∀ s, Std.Iterators.Iterator (σ s) Id (SearchStep s)]
variable [∀ s, Std.Iterators.Finite (σ s) Id]
variable [∀ s, Std.Iterators.IteratorLoop (σ s) Id Id]

@[inline]
def endsWith [BackwardPattern ρ] (s : Slice) (pat : ρ) : Bool :=
  BackwardPattern.endsWith s pat

inductive RevSplitIterator (ρ : Type) [ToBackwardSearcher ρ σ] where
  | operating (s : Slice) (currPos : s.Pos) (searcher : Std.Iter (α := σ s) (SearchStep s))
  | atEnd
  deriving Inhabited

namespace RevSplitIterator

variable [ToBackwardSearcher ρ σ]

instance [Pure m] : Std.Iterators.Iterator (RevSplitIterator ρ) m Slice where
  IsPlausibleStep := fun _ _ => True
  step := fun ⟨iter⟩ =>
    match iter with
    | .operating s currPos searcher =>
      match Internal.nextMatch searcher with
      | some (searcher, startPos, endPos) =>
        let slice := s.replaceStartEnd! endPos currPos
        let nextIt := ⟨.operating s startPos searcher⟩
        pure ⟨.yield nextIt slice, by simp⟩
      | none =>
        if currPos ≠ s.startPos then
          let slice := s.replaceEnd currPos
          pure ⟨.yield ⟨.atEnd⟩ slice, by simp⟩
        else
          pure ⟨.done, by simp⟩
    | .atEnd => pure ⟨.done, by simp⟩

-- TODO: Finiteness after we have a notion of lawful searcher

instance [Monad m] [Monad n] : Std.Iterators.IteratorCollect (RevSplitIterator ρ) m n :=
  .defaultImplementation

instance [Monad m] [Monad n] :
    Std.Iterators.IteratorCollectPartial (RevSplitIterator ρ) m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorLoop (RevSplitIterator ρ) m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorLoopPartial (RevSplitIterator ρ) m n :=
  .defaultImplementation

end RevSplitIterator

@[specialize pat]
def revSplit [ToBackwardSearcher ρ σ] (s : Slice) (pat : ρ) :
    Std.Iter (α := RevSplitIterator ρ) Slice :=
  { internalState := .operating s s.endPos (ToBackwardSearcher.toSearcher s pat) }

@[inline]
def dropEnd (s : Slice) (n : Nat) : Slice :=
  s.replaceEnd (s.endPos.prevn n)

@[specialize pat]
def dropEndWhile [ToBackwardSearcher ρ σ] (s : Slice) (pat : ρ) : Slice :=
  let searcher := ToBackwardSearcher.toSearcher s pat
  match Internal.nextReject searcher with
  | some (_, _, endPos) => s.replaceEnd endPos
  | none => s.replaceEnd s.startPos

-- If we want to optimize this can be pushed further by specialising for ASCII
@[inline]
def trimAsciiEnd (s : Slice) : Slice :=
  dropEndWhile s Char.isWhitespace

@[inline]
def takeEnd (s : Slice) (n : Nat) : Slice :=
  s.replaceStart (s.startPos.prevn n)

@[specialize pat]
def takeEndWhile [ToBackwardSearcher ρ σ] (s : Slice) (pat : ρ) : Slice :=
  let searcher := ToBackwardSearcher.toSearcher s pat
  match Internal.nextReject searcher with
  | some (_, _, endPos) => s.replaceStart endPos
  | none => s

@[inline]
def dropSuffix? [BackwardPattern ρ] (s : Slice) (pat : ρ) : Option Slice :=
  BackwardPattern.dropSuffix? s pat

@[specialize pat]
def dropSuffix [BackwardPattern ρ] (s : Slice) (pat : ρ) : Slice :=
  dropSuffix? s pat |>.getD s

@[specialize pat]
def revFind? [ToBackwardSearcher ρ σ] (s : Slice) (pat : ρ) : Option s.Pos :=
  let searcher := ToBackwardSearcher.toSearcher s pat
  match Internal.nextMatch searcher with
  | some (_, startPos, _) => some startPos
  | none => none

end BackwardPatternUsers

def trimAscii (s : Slice) : Slice :=
  s.trimAsciiStart.trimAsciiEnd

def eqIgnoreAsciiCase (s1 s2 : Slice) : Bool :=
  s1.utf8ByteSize == s2.utf8ByteSize && go s1 s1.startPos.offset s2 s2.startPos.offset
where
  go (s1 : Slice) (s1Curr : String.Pos) (s2 : Slice) (s2Curr : String.Pos) : Bool :=
    if h : s1Curr < s1.utf8ByteSize ∧ s2Curr < s2.utf8ByteSize then
      let c1 := (s1.getUtf8Byte s1Curr h.left).toAsciiLower
      let c2 := (s2.getUtf8Byte s2Curr h.right).toAsciiLower
      if c1 == c2 then
        go s1 s1Curr.inc s2 s2Curr.inc
      else
        false
    else
      s1Curr == s1.utf8ByteSize && s2Curr == s2.utf8ByteSize
  termination_by s1.endPos.offset.byteIdx - s1Curr.byteIdx
  decreasing_by
    simp at h ⊢
    omega

def beq (s1 s2 : Slice) : Bool :=
  if h : s1.utf8ByteSize = s2.utf8ByteSize then
    have h1 := by simp [h, String.Pos.le_iff]
    have h2 := by simp [h, String.Pos.le_iff]
    Internal.memcmp s1 s2 s1.startPos.offset s2.startPos.offset s1.utf8ByteSize h1 h2
  else
    false

instance : BEq Slice where
  beq := beq

@[extern "lean_slice_hash"]
opaque hash (s : Slice) : UInt64

instance : Hashable Slice where
  hash := hash

instance : LT Slice where
  lt x y := x.copy < y.copy

@[extern "lean_slice_dec_lt"]
instance : DecidableLT Slice :=
  fun x y => inferInstanceAs (Decidable (x.copy < y.copy))

instance : Ord Slice where
  compare x y := compareOfLessAndBEq x y

structure CharIterator where
  s : Slice
  currPos : s.Pos
  deriving Inhabited

def chars (s : Slice) : Std.Iter (α := CharIterator) Char :=
  { internalState := { s, currPos := s.startPos }}

namespace CharIterator

instance [Pure m] : Std.Iterators.Iterator CharIterator m Char where
  IsPlausibleStep it
    | .yield it' out =>
      ∃ h1 : it.internalState.s = it'.internalState.s,
      ∃ h2 : it.internalState.currPos ≠ it.internalState.s.endPos,
        it'.internalState.currPos = h1 ▸ (it.internalState.currPos.next h2) ∧
        it.internalState.currPos.get h2 = out
    | .skip _ => False
    | .done => it.internalState.currPos = it.internalState.s.endPos
  step := fun ⟨s, currPos⟩ =>
    if h : currPos = s.endPos then
      pure ⟨.done, by simp [h]⟩
    else
      pure ⟨.yield ⟨s, currPos.next h⟩ (currPos.get h), by simp [h]⟩

private def finitenessRelation [Pure m] : Std.Iterators.FinitenessRelation CharIterator m where
  rel := InvImage WellFoundedRelation.rel
      (fun it => it.internalState.s.utf8ByteSize.byteIdx - it.internalState.currPos.offset.byteIdx)
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by
    simp_wf
    obtain ⟨step, h, h'⟩ := h
    cases step
    · cases h
      obtain ⟨h1, h2, h3, _⟩ := h'
      have h4 := Char.utf8Size_pos (it.internalState.currPos.get h2)
      have h5 := it.internalState.currPos.isValidForSlice.le_utf8ByteSize
      rw [h3]
      clear h3
      generalize it'.internalState.s = s at *
      cases h1
      simp [Pos.ext_iff, String.Pos.ext_iff, Pos.le_iff] at h2 h4 h5 ⊢
      omega
    · cases h'
    · cases h

@[no_expose]
instance [Pure m] : Std.Iterators.Finite CharIterator m :=
  .of_finitenessRelation finitenessRelation

instance [Monad m] [Monad n] : Std.Iterators.IteratorCollect CharIterator m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorCollectPartial CharIterator m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorLoop CharIterator m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorLoopPartial CharIterator m n :=
  .defaultImplementation

end CharIterator

structure RevCharIterator where
  s : Slice
  currPos : s.Pos
  deriving Inhabited

def revChars (s : Slice) : Std.Iter (α := RevCharIterator) Char :=
  { internalState := { s, currPos := s.endPos }}

namespace RevCharIterator

instance [Pure m] : Std.Iterators.Iterator RevCharIterator m Char where
  IsPlausibleStep it
    | .yield it' out =>
      ∃ h1 : it.internalState.s = it'.internalState.s,
      ∃ h2 : it.internalState.currPos ≠ it.internalState.s.startPos,
        it'.internalState.currPos = h1 ▸ (it.internalState.currPos.prev h2) ∧
        (it.internalState.currPos.prev h2).get Pos.prev_ne_endPos = out
    | .skip _ => False
    | .done => it.internalState.currPos = it.internalState.s.startPos
  step := fun ⟨s, currPos⟩ =>
    if h : currPos = s.startPos then
      pure ⟨.done, by simp [h]⟩
    else
      let nextPos := currPos.prev h
      pure ⟨.yield ⟨s, nextPos⟩ (nextPos.get Pos.prev_ne_endPos), by simp [h, nextPos]⟩

private def finitenessRelation [Pure m] :
    Std.Iterators.FinitenessRelation RevCharIterator m where
  rel := InvImage WellFoundedRelation.rel
      (fun it => it.internalState.currPos.offset.byteIdx)
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by
    simp_wf
    obtain ⟨step, h, h'⟩ := h
    cases step
    · cases h
      obtain ⟨h1, h2, h3, _⟩ := h'
      rw [h3]
      clear h3
      generalize it'.internalState.s = s at *
      cases h1
      have h4 := Pos.offset_prev_lt_offset (h := h2)
      simp
      omega
    · cases h'
    · cases h

@[no_expose]
instance [Pure m] : Std.Iterators.Finite RevCharIterator m :=
  .of_finitenessRelation finitenessRelation

instance [Monad m] [Monad n] : Std.Iterators.IteratorCollect RevCharIterator m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorCollectPartial RevCharIterator m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorLoop RevCharIterator m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorLoopPartial RevCharIterator m n :=
  .defaultImplementation

end RevCharIterator

structure PosIterator (s : Slice) where
  currPos : s.Pos
  deriving Inhabited

def positions (s : Slice) : Std.Iter (α := PosIterator s) s.Pos :=
  { internalState := { currPos := s.startPos }}

namespace PosIterator

instance [Pure m] : Std.Iterators.Iterator (PosIterator s) m s.Pos where
  IsPlausibleStep it
    | .yield it' out =>
      ∃ h : it.internalState.currPos ≠ s.endPos,
        it'.internalState.currPos = it.internalState.currPos.next h ∧
        it.internalState.currPos = out
    | .skip _ => False
    | .done => it.internalState.currPos = s.endPos
  step := fun ⟨⟨currPos⟩⟩ =>
    if h : currPos = s.endPos then
      pure ⟨.done, by simp [h]⟩
    else
      pure ⟨.yield ⟨⟨currPos.next h⟩⟩ currPos, by simp [h]⟩

private def finitenessRelation [Pure m] :
    Std.Iterators.FinitenessRelation (PosIterator s) m where
  rel := InvImage WellFoundedRelation.rel
      (fun it => s.utf8ByteSize.byteIdx - it.internalState.currPos.offset.byteIdx)
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by
    simp_wf
    obtain ⟨step, h, h'⟩ := h
    cases step
    · cases h
      obtain ⟨h1, h2, _⟩ := h'
      have h3 := Char.utf8Size_pos (it.internalState.currPos.get h1)
      have h4 := it.internalState.currPos.isValidForSlice.le_utf8ByteSize
      simp [Pos.ext_iff, String.Pos.ext_iff, Pos.le_iff] at h1 h2 h4
      omega
    · cases h'
    · cases h

@[no_expose]
instance [Pure m] : Std.Iterators.Finite (PosIterator s) m :=
  .of_finitenessRelation finitenessRelation

instance [Monad m] [Monad n] : Std.Iterators.IteratorCollect (PosIterator s) m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorCollectPartial (PosIterator s) m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorLoop (PosIterator s) m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorLoopPartial (PosIterator s) m n :=
  .defaultImplementation

end PosIterator

structure RevPosIterator (s : Slice) where
  currPos : s.Pos
  deriving Inhabited

def revPositions (s : Slice) : Std.Iter (α := RevPosIterator s) s.Pos :=
  { internalState := { currPos := s.endPos }}

namespace RevPosIterator

instance [Pure m] : Std.Iterators.Iterator (RevPosIterator s) m s.Pos where
  IsPlausibleStep it
    | .yield it' out =>
      ∃ h : it.internalState.currPos ≠ s.startPos,
        it'.internalState.currPos = it.internalState.currPos.prev h ∧
        it.internalState.currPos.prev h = out
    | .skip _ => False
    | .done => it.internalState.currPos = s.startPos
  step := fun ⟨⟨currPos⟩⟩ =>
    if h : currPos = s.startPos then
      pure ⟨.done, by simp [h]⟩
    else
      let prevPos := currPos.prev h
      pure ⟨.yield ⟨⟨prevPos⟩⟩ prevPos, by simp [h, prevPos]⟩

private def finitenessRelation [Pure m] :
    Std.Iterators.FinitenessRelation (RevPosIterator s) m where
  rel := InvImage WellFoundedRelation.rel
      (fun it => it.internalState.currPos.offset.byteIdx)
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by
    simp_wf
    obtain ⟨step, h, h'⟩ := h
    cases step
    · cases h
      obtain ⟨h1, h2, _⟩ := h'
      have h3 := Pos.offset_prev_lt_offset (h := h1)
      simp [Pos.ext_iff, String.Pos.ext_iff] at h2 h3
      omega
    · cases h'
    · cases h

@[no_expose]
instance [Pure m] : Std.Iterators.Finite (RevPosIterator s) m :=
  .of_finitenessRelation finitenessRelation

instance [Monad m] [Monad n] : Std.Iterators.IteratorCollect (RevPosIterator s) m n :=
  .defaultImplementation

instance [Monad m] [Monad n] :
    Std.Iterators.IteratorCollectPartial (RevPosIterator s) m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorLoop (RevPosIterator s) m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorLoopPartial (RevPosIterator s) m n :=
  .defaultImplementation

end RevPosIterator

structure ByteIterator where
  s : Slice
  offset : String.Pos
  deriving Inhabited

def bytes (s : Slice) : Std.Iter (α := ByteIterator) UInt8 :=
  { internalState := { s, offset := s.startPos.offset }}

namespace ByteIterator

instance [Pure m] : Std.Iterators.Iterator ByteIterator m UInt8 where
  IsPlausibleStep it
    | .yield it' out =>
      ∃ h1 : it.internalState.offset < it.internalState.s.utf8ByteSize,
        it.internalState.s = it'.internalState.s ∧
        it'.internalState.offset = it.internalState.offset.inc ∧
        it.internalState.s.getUtf8Byte it.internalState.offset h1 = out
    | .skip _ => False
    | .done => ¬ it.internalState.offset < it.internalState.s.utf8ByteSize
  step := fun ⟨s, offset⟩ =>
    if h : offset < s.utf8ByteSize then
      pure ⟨.yield ⟨s, offset.inc⟩ (s.getUtf8Byte offset h), by simp [h]⟩
    else
      pure ⟨.done, by simp [h]⟩

private def finitenessRelation [Pure m] :
    Std.Iterators.FinitenessRelation (ByteIterator) m where
  rel := InvImage WellFoundedRelation.rel
      (fun it => it.internalState.s.utf8ByteSize.byteIdx - it.internalState.offset.byteIdx)
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
      simp [String.Pos.ext_iff] at h1 h3
      omega
    · cases h'
    · cases h

@[no_expose]
instance [Pure m] : Std.Iterators.Finite ByteIterator m :=
  .of_finitenessRelation finitenessRelation

instance [Monad m] [Monad n] : Std.Iterators.IteratorCollect ByteIterator m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorCollectPartial ByteIterator m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorLoop ByteIterator m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorLoopPartial ByteIterator m n :=
  .defaultImplementation

end ByteIterator

structure RevByteIterator where
  s : Slice
  offset : String.Pos
  hinv : offset ≤ s.utf8ByteSize

def revBytes (s : Slice) : Std.Iter (α := RevByteIterator) UInt8 :=
  { internalState := { s, offset := s.endPos.offset, hinv := by simp }}

instance : Inhabited RevByteIterator where
  default :=
    let s := default
    { s := s, offset := s.endPos.offset, hinv := by simp}

namespace RevByteIterator

instance [Pure m] : Std.Iterators.Iterator RevByteIterator m UInt8 where
  IsPlausibleStep it
    | .yield it' out =>
      ∃ h1 : it.internalState.offset.dec < it.internalState.s.utf8ByteSize,
        it.internalState.s = it'.internalState.s ∧
        it.internalState.offset ≠ 0 ∧
        it'.internalState.offset = it.internalState.offset.dec ∧
        it.internalState.s.getUtf8Byte it.internalState.offset.dec h1 = out
    | .skip _ => False
    | .done => it.internalState.offset = 0
  step := fun ⟨s, offset, hinv⟩ =>
    if h : offset ≠ 0 then
      let nextOffset := offset.dec
      have hbound := by
        simp [String.Pos.le_iff, nextOffset] at h hinv ⊢
        omega
      have hinv := by
        simp [String.Pos.le_iff, nextOffset] at hinv ⊢
        omega
      have hiter := by simp [nextOffset, hbound, h]
      pure ⟨.yield ⟨s, nextOffset, hinv⟩ (s.getUtf8Byte nextOffset hbound), hiter⟩
    else
      pure ⟨.done, by simpa using h⟩

private def finitenessRelation [Pure m] :
    Std.Iterators.FinitenessRelation (RevByteIterator) m where
  rel := InvImage WellFoundedRelation.rel
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

instance [Monad m] [Monad n] : Std.Iterators.IteratorCollect RevByteIterator m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorCollectPartial RevByteIterator m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorLoop RevByteIterator m n :=
  .defaultImplementation

instance [Monad m] [Monad n] : Std.Iterators.IteratorLoopPartial RevByteIterator m n :=
  .defaultImplementation

end RevByteIterator

def lines.lineMap (s : Slice) : Slice :=
  if let some s := s.dropSuffix? '\n' then
    if let some s := s.dropSuffix? '\r' then
      s
    else
      s
  else
    s

def lines (s : Slice) :=
  s.splitInclusive '\n' |>.map lines.lineMap

end String.Slice
