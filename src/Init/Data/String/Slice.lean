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

set_option doc.verso true

/-!
This module defines the programming API for {name}`String.Slice`. The API mostly consists of
functionality for searching for various kinds of pattern matches in slices to iterate over them,
provide subslices according to matches etc. The key design principles behind this module are:
- Instead of providing one function per kind of pattern the API is generic over various kinds of
  patterns. Thus it only provides e.g. one kind of function for looking for the position of the
  first occurence of a pattern. Currently the supported patterns are:
  - {name}`Char`
  - {lean}`Char → Bool`
  - {name}`String` and {name}`String.Slice` (partially: doing non trivial searches backwards is not
    supported yet)
- Whenever a slice gets mutated a new slice is returned to allow for repeated chaining of functions
  with minimal allocations. If necessary the slice can ultimately be converted back to
  {name}`String` using {name}`String.Slice.copy`
- Instead of allocating intermediate collections the operations that iterate over slices in various
  ways (characters, positions etc.) return iterators that can be collected into other collections if
  necessary.
- When sensible the API provides functionality for searching both in a forward and backward manner
-/

public section

namespace String.Slice

open Pattern

/--
Checks whether a slice is empty.

Empty slices have {name}`utf8ByteSize` {lean}`0`.

Examples:
 * {lean}`"".toSlice.isEmpty = true`
 * {lean}`" ".toSlice.isEmpty = false`
-/
@[inline]
def isEmpty (s : Slice) : Bool := s.utf8ByteSize == 0

/--
Checks whether {name}`s1` and {name}`s2` represent the same string, even if they are slices of
different base strings or different slices within the same string.

The implementation is an efficient equivalent of {lean}`s1.copy == s2.copy`
-/
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

section ForwardPatternUsers

variable {ρ : Type} {σ : Slice → Type}
variable [∀ s, Std.Iterators.Iterator (σ s) Id (SearchStep s)]
variable [∀ s, Std.Iterators.Finite (σ s) Id]
variable [∀ s, Std.Iterators.IteratorLoop (σ s) Id Id]

/--
Checks whether the slice ({name}`s`) begins with the pattern ({name}`pat`).

This function is generic over all currently supported patterns.

Examples:
 * {lean}`"red green blue".toSlice.startsWith "red" = true`
 * {lean}`"red green blue".toSlice.startsWith "green" = false`
 * {lean}`"red green blue".toSlice.startsWith "" = true`
 * {lean}`"red green blue".toSlice.startsWith 'r' = true`
 * {lean}`"red green blue".toSlice.startsWith Char.isLower = true`
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
Splits a slice at each subslice that matches the pattern {name}`pat`.

The subslices that matched the pattern are not included in any of the resulting subslices. If
multiple subslices in a row match the pattern, the resulting list will contain empty strings.

This function is generic over all currently supported patterns.

Examples:
 * {lean}`("coffee tea water".toSlice.split Char.isWhitespace).allowNontermination.toList == ["coffee".toSlice, "tea".toSlice, "water".toSlice]`
 * {lean}`("coffee tea water".toSlice.split ' ').allowNontermination.toList == ["coffee".toSlice, "tea".toSlice, "water".toSlice]`
 * {lean}`("coffee tea water".toSlice.split " tea ").allowNontermination.toList == ["coffee".toSlice, "water".toSlice]`
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
Splits a slice at each subslice that matches the pattern {name}`pat`. Unlike {name}`split` the
matched subslices are included at the end of each subslice.

This function is generic over all currently supported patterns.

Examples:
 * {lean}`("coffee tea water".toSlice.splitInclusive Char.isWhitespace).allowNontermination.toList == ["coffee ".toSlice, "tea ".toSlice, "water".toSlice]`
 * {lean}`("coffee tea water".toSlice.splitInclusive ' ').allowNontermination.toList == ["coffee ".toSlice, "tea ".toSlice, "water".toSlice]`
 * {lean}`("coffee tea water".toSlice.splitInclusive " tea ").allowNontermination.toList == ["coffee tea ".toSlice, "water".toSlice]`
-/
@[specialize pat]
def splitInclusive [ToForwardSearcher ρ σ] (s : Slice) (pat : ρ) :
    Std.Iter (α := SplitInclusiveIterator ρ) Slice :=
  { internalState := .operating s s.startPos (ToForwardSearcher.toSearcher s pat) }

/--
If {name}`pat` matches a prefix of {name}`s`, returns the remainder. Returns {name}`none` otherwise.

Use {name (scope := "Init.Data.String.Slice")}`String.Slice.dropPrefix` to return the slice
unchanged when {name}`pat` does not match a prefix.

This function is generic over all currently supported patterns.

Examples:
 * {lean}`"red green blue".toSlice.dropPrefix? "red " == some "green blue".toSlice`
 * {lean}`"red green blue".toSlice.dropPrefix? "reed " == none`
 * {lean}`"red green blue".toSlice.dropPrefix? 'r' == some "ed green blue".toSlice`
 * {lean}`"red green blue".toSlice.dropPrefix? Char.isLower == some "ed green blue".toSlice`
-/
@[inline]
def dropPrefix? [ForwardPattern ρ] (s : Slice) (pat : ρ) : Option Slice :=
  ForwardPattern.dropPrefix? s pat

/--
If {name}`pat` matches a prefix of {name}`s`, returns the remainder. Returns {name}`s` unmodified
otherwise.

Use {name}`String.Slice.dropPrefix?` to return {name}`none` when {name}`pat` does not match a prefix.

This function is generic over all currently supported patterns.

Examples:
 * {lean}`"red green blue".toSlice.dropPrefix "red " == "green blue".toSlice`
 * {lean}`"red green blue".toSlice.dropPrefix "reed " == "red green blue".toSlice`
 * {lean}`"red green blue".toSlice.dropPrefix 'r' == "ed green blue".toSlice`
 * {lean}`"red green blue".toSlice.dropPrefix Char.isLower == "ed green blue".toSlice`
-/
@[specialize pat]
def dropPrefix [ForwardPattern ρ] (s : Slice) (pat : ρ) : Slice :=
  dropPrefix? s pat |>.getD s

/--
Removes the specified number of characters (Unicode code points) from the start of the slice.

If {name}`n` is greater than the amount of characters in {name}`s`, returns an empty slice.

Examples:
 * {lean}`"red green blue".toSlice.drop 4 == "green blue".toSlice`
 * {lean}`"red green blue".toSlice.drop 10 == "blue".toSlice`
 * {lean}`"red green blue".toSlice.drop 50 == "".toSlice`
-/
@[inline]
def drop (s : Slice) (n : Nat) : Slice :=
  s.replaceStart (s.startPos.nextn n)

/--
Creates a new slice that contains the longest prefix of {name}`s` for which {name}`pat` matched
(potentially repeatedly).

Examples:
 * {lean}`"red green blue".toSlice.dropWhile Char.isLower == " green blue".toSlice`
 * {lean}`"red green blue".toSlice.dropWhile 'r' == "ed green blue".toSlice`
 * {lean}`"red red green blue".toSlice.dropWhile "red " == "green blue".toSlice`
 * {lean}`"red green blue".toSlice.dropWhile (fun (_ : Char) => true) == "".toSlice`
-/
@[inline]
partial def dropWhile [ForwardPattern ρ] (s : Slice) (pat : ρ) : Slice :=
  go s
where
  @[specialize pat]
  go (s : Slice) : Slice :=
    if let some nextS := dropPrefix? s pat then
      -- TODO: need lawful patterns to show this terminates
      if s.startInclusive.offset < nextS.startInclusive.offset then
        go nextS
      else
        s
    else
      s

/--
Removes leading whitespace from a slice by moving its start position to the first non-whitespace
character, or to its end position if there is no non-whitespace character.

“Whitespace” is defined as characters for which {name}`Char.isWhitespace` returns {name}`true`.

Examples:
 * {lean}`"abc".toSlice.trimAsciiStart == "abc".toSlice`
 * {lean}`"   abc".toSlice.trimAsciiStart == "abc".toSlice`
 * {lean}`"abc \t  ".toSlice.trimAsciiStart == "abc \t  ".toSlice`
 * {lean}`"  abc   ".toSlice.trimAsciiStart == "abc   ".toSlice`
 * {lean}`"abc\ndef\n".toSlice.trimAsciiStart == "abc\ndef\n".toSlice`
-/
@[inline]
def trimAsciiStart (s : Slice) : Slice :=
  -- If we want to optimize this can be pushed further by specialising for ASCII
  dropWhile s Char.isWhitespace

/--
Creates a new slice that contains the first {name}`n` characters (Unicode code points) of {name}`s`.

If {name}`n` is greater than the amount of characters in {name}`s`, returns {name}`s`.

Examples:
 * {lean}`"red green blue".toSlice.take 3 == "red".toSlice`
 * {lean}`"red green blue".toSlice.take 1 == "r".toSlice`
 * {lean}`"red green blue".toSlice.take 0 == "".toSlice`
 * {lean}`"red green blue".toSlice.take 100 == "red green blue".toSlice`
-/
@[inline]
def take (s : Slice) (n : Nat) : Slice :=
  s.replaceEnd (s.startPos.nextn n)

/--
Creates a new slice that contains the longest prefix of {name}`s` for which {name}`pat` matched
(potentially repeatedly).

This function is generic over all currently supported patterns.

Examples:
 * {lean}`"red green blue".toSlice.takeWhile Char.isLower == "red".toSlice`
 * {lean}`"red green blue".toSlice.takeWhile 'r' == "r".toSlice`
 * {lean}`"red red green blue".toSlice.takeWhile "red " == "red red ".toSlice`
 * {lean}`"red green blue".toSlice.takeWhile (fun (_ : Char) => true) == "red green blue".toSlice`
-/
@[inline]
partial def takeWhile [ForwardPattern ρ] (s : Slice) (pat : ρ) : Slice :=
  go s
where
  @[specialize pat]
  go (curr : Slice) : Slice :=
    if let some nextCurr := dropPrefix? curr pat then
      if curr.startInclusive.offset < nextCurr.startInclusive.offset then
        -- TODO: need lawful patterns to show this terminates
        go nextCurr
      else
        s.replaceEnd <| s.pos! <| curr.startInclusive.offset
    else
      s.replaceEnd <| s.pos! <| curr.startInclusive.offset

/--
Finds the position of the first match of the pattern {name}`pat` in a slice {name}`true`. If there
is no match {name}`none` is returned.

This function is generic over all currently supported patterns.

Examples:
 * {lean}`("coffee tea water".toSlice.find? Char.isWhitespace).map (·.get!) == some ' '`
 * {lean}`"tea".toSlice.find? (fun (c : Char) => c == 'X') == none`
 * {lean}`("coffee tea water".toSlice.find? "tea").map (·.get!) == some 't'`
-/
@[specialize pat]
def find? [ToForwardSearcher ρ σ] (s : Slice) (pat : ρ) : Option s.Pos :=
  let searcher := ToForwardSearcher.toSearcher s pat
  match Internal.nextMatch searcher with
  | some (_, startPos, _) => some startPos
  | none => none

/--
Checks whether a slice has a match of the pattern {name}`pat` anywhere.

This function is generic over all currently supported patterns.

Examples:
 * {lean}`"coffee tea water".toSlice.contains Char.isWhitespace = true`
 * {lean}`"tea".toSlice.contains (fun (c : Char) => c == 'X') = false`
 * {lean}`"coffee tea water".toSlice.contains "tea" = true`
-/
@[specialize pat]
def contains [ToForwardSearcher ρ σ] (s : Slice) (pat : ρ) : Bool :=
  let searcher := ToForwardSearcher.toSearcher s pat
  Internal.nextMatch searcher |>.isSome

/--
Checks whether a slice only consists of matches of the pattern {name}`pat` anywhere.

Short-circuits at the first pattern mis-match.

This function is generic over all currently supported patterns.

Examples:
 * {lean}`"brown".toSlice.all Char.isLower = true`
 * {lean}`"brown and orange".toSlice.all Char.isLower = false`
 * {lean}`"aaaaaa".toSlice.all 'a' = true`
 * {lean}`"aaaaaa".toSlice.all "aa" = true`
-/
@[inline]
def all [ForwardPattern ρ] (s : Slice) (pat : ρ) : Bool :=
  s.dropWhile pat |>.isEmpty

end ForwardPatternUsers

section BackwardPatternUsers

variable {σ : Slice → Type}
variable [∀ s, Std.Iterators.Iterator (σ s) Id (SearchStep s)]
variable [∀ s, Std.Iterators.Finite (σ s) Id]
variable [∀ s, Std.Iterators.IteratorLoop (σ s) Id Id]

/--
Checks whether the slice ({name}`s`) ends with the pattern ({name}`pat`).

This function is generic over all currently supported patterns.

Examples:
 * {lean}`"red green blue".toSlice.endsWith "blue" = true`
 * {lean}`"red green blue".toSlice.endsWith "green" = false`
 * {lean}`"red green blue".toSlice.endsWith "" = true`
 * {lean}`"red green blue".toSlice.endsWith 'e' = true`
 * {lean}`"red green blue".toSlice.endsWith Char.isLower = true`
-/
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

/--
Splits a slice at each subslice that matches the pattern {name}`pat`, starting from the end of the
slice and traversing towards the start.

The subslices that matched the pattern are not included in any of the resulting subslices. If
multiple subslices in a row match the pattern, the resulting list will contain empty slices.

This function is generic over all currently supported patterns except
{name}`String`/{name}`String.Slice`.

Examples:
 * {lean}`("coffee tea water".toSlice.revSplit Char.isWhitespace).allowNontermination.toList == ["water".toSlice, "tea".toSlice, "coffee".toSlice]`
 * {lean}`("coffee tea water".toSlice.revSplit ' ').allowNontermination.toList == ["water".toSlice, "tea".toSlice, "coffee".toSlice]`
-/
@[specialize pat]
def revSplit [ToBackwardSearcher ρ σ] (s : Slice) (pat : ρ) :
    Std.Iter (α := RevSplitIterator ρ) Slice :=
  { internalState := .operating s s.endPos (ToBackwardSearcher.toSearcher s pat) }

/--
If {name}`pat` matches a suffix of {name}`s`, returns the remainder. Returns {name}`none` otherwise.

Use {name (scope := "Init.Data.String.Slice")}`String.Slice.dropSuffix` to return the slice
unchanged when {name}`pat` does not match a prefix.

This function is generic over all currently supported patterns.

Examples:
 * {lean}`"red green blue".toSlice.dropSuffix? " blue" == some "red green".toSlice`
 * {lean}`"red green blue".toSlice.dropSuffix? "bluu " == none`
 * {lean}`"red green blue".toSlice.dropSuffix? 'e' == some "red green blu".toSlice`
 * {lean}`"red green blue".toSlice.dropSuffix? Char.isLower == some "red green blu".toSlice`
-/
@[inline]
def dropSuffix? [BackwardPattern ρ] (s : Slice) (pat : ρ) : Option Slice :=
  BackwardPattern.dropSuffix? s pat

/--
If {name}`pat` matches a suffix of {name}`s`, returns the remainder. Returns {name}`s` unmodified
otherwise.

Use {name}`String.Slice.dropSuffix?` to return {name}`none` when {name}`pat` does not match a
prefix.

This function is generic over all currently supported patterns.

Examples:
 * {lean}`"red green blue".toSlice.dropSuffix " blue" == "red green".toSlice`
 * {lean}`"red green blue".toSlice.dropSuffix "bluu " == "red green blue".toSlice`
 * {lean}`"red green blue".toSlice.dropSuffix 'e' == "red green blu".toSlice`
 * {lean}`"red green blue".toSlice.dropSuffix Char.isLower == "red green blu".toSlice`
-/
@[specialize pat]
def dropSuffix [BackwardPattern ρ] (s : Slice) (pat : ρ) : Slice :=
  dropSuffix? s pat |>.getD s

/--
Removes the specified number of characters (Unicode code points) from the end of the slice.

If {name}`n` is greater than the amount of characters in {name}`s`, returns an empty slice.

Examples:
 * {lean}`"red green blue".toSlice.dropEnd 5 == "red green".toSlice`
 * {lean}`"red green blue".toSlice.dropEnd 11 == "red".toSlice`
 * {lean}`"red green blue".toSlice.dropEnd 50 == "".toSlice`
-/
@[inline]
def dropEnd (s : Slice) (n : Nat) : Slice :=
  s.replaceEnd (s.endPos.prevn n)

/--
Creates a new slice that contains the longest suffix of {name}`s` for which {name}`pat` matched
(potentially repeatedly).

Examples:
 * {lean}`"red green blue".toSlice.dropEndWhile Char.isLower == "red green ".toSlice`
 * {lean}`"red green blue".toSlice.dropEndWhile 'e' == "red green blu".toSlice`
 * {lean}`"red green blue".toSlice.dropEndWhile (fun (_ : Char) => true) == "".toSlice`
-/
@[inline]
partial def dropEndWhile [BackwardPattern ρ] (s : Slice) (pat : ρ) : Slice :=
  go s
where
  @[specialize pat]
  go (s : Slice) : Slice :=
    if let some nextS := dropSuffix? s pat then
      -- TODO: need lawful patterns to show this terminates
      if nextS.endExclusive.offset < s.endExclusive.offset then
        go nextS
      else
        s
    else
      s

/--
Removes trailing whitespace from a slice by moving its start position to the first non-whitespace
character, or to its end position if there is no non-whitespace character.

“Whitespace” is defined as characters for which {name}`Char.isWhitespace` returns {name}`true`.

Examples:
 * {lean}`"abc".toSlice.trimAsciiEnd == "abc".toSlice`
 * {lean}`"   abc".toSlice.trimAsciiEnd == "   abc".toSlice`
 * {lean}`"abc \t  ".toSlice.trimAsciiEnd == "abc".toSlice`
 * {lean}`"  abc   ".toSlice.trimAsciiEnd == "  abc".toSlice`
 * {lean}`"abc\ndef\n".toSlice.trimAsciiEnd == "abc\ndef".toSlice`
-/
@[inline]
def trimAsciiEnd (s : Slice) : Slice :=
  -- If we want to optimize this can be pushed further by specialising for ASCII
  dropEndWhile s Char.isWhitespace

/--
Creates a new slice that contains the last {name}`n` characters (Unicode code points) of {name}`s`.

If {name}`n` is greater than the amount of characters in {name}`s`, returns {name}`s`.

Examples:
 * {lean}`"red green blue".toSlice.takeEnd 4 == "blue".toSlice`
 * {lean}`"red green blue".toSlice.takeEnd 1 == "e".toSlice`
 * {lean}`"red green blue".toSlice.takeEnd 0 == "".toSlice`
 * {lean}`"red green blue".toSlice.takeEnd 100 == "red green blue".toSlice`
-/
@[inline]
def takeEnd (s : Slice) (n : Nat) : Slice :=
  s.replaceStart (s.endPos.prevn n)

/--
Creates a new slice that contains the suffix prefix of {name}`s` for which {name}`pat` matched
(potentially repeatedly).

This function is generic over all currently supported patterns.

Examples:
 * {lean}`"red green blue".toSlice.takeEndWhile Char.isLower == "blue".toSlice`
 * {lean}`"red green blue".toSlice.takeEndWhile 'e' == "e".toSlice`
 * {lean}`"red green blue".toSlice.takeEndWhile (fun (_ : Char) => true) == "red green blue".toSlice`
-/
@[inline]
partial def takeEndWhile [BackwardPattern ρ] (s : Slice) (pat : ρ) : Slice :=
  go s
where
  @[specialize pat]
  go (curr : Slice) : Slice :=
    if let some nextCurr := dropSuffix? curr pat then
      if nextCurr.endExclusive.offset < curr.endExclusive.offset then
        -- TODO: need lawful patterns to show this terminates
        go nextCurr
      else
        s.replaceStart <| s.pos! <| curr.endExclusive.offset
    else
      s.replaceStart <| s.pos! <| curr.endExclusive.offset

/--
Finds the position of the first match of the pattern {name}`pat` in a slice {name}`true`, starting
from the end of the slice and traversing towards the start. If there is no match {name}`none` is
returned.

This function is generic over all currently supported patterns except
{name}`String`/{name}`String.Slice`.

Examples:
 * {lean}`("coffee tea water".toSlice.find? Char.isWhitespace).map (·.get!) == some ' '`
 * {lean}`"tea".toSlice.find? (fun (c : Char) => c == 'X') == none`
 * {lean}`("coffee tea water".toSlice.find? "tea").map (·.get!) == some 't'`
-/
@[specialize pat]
def revFind? [ToBackwardSearcher ρ σ] (s : Slice) (pat : ρ) : Option s.Pos :=
  let searcher := ToBackwardSearcher.toSearcher s pat
  match Internal.nextMatch searcher with
  | some (_, startPos, _) => some startPos
  | none => none

end BackwardPatternUsers

/--
Removes leading and trailing whitespace from a slice.

“Whitespace” is defined as characters for which {name}`Char.isWhitespace` returns {name}`true`.

Examples:
 * {lean}`"abc".toSlice.trimAscii == "abc".toSlice`
 * {lean}`"   abc".toSlice.trimAscii == "abc".toSlice`
 * {lean}`"abc \t  ".toSlice.trimAscii == "abc".toSlice`
 * {lean}`"  abc   ".toSlice.trimAscii == "abc".toSlice`
 * {lean}`"abc\ndef\n".toSlice.trimAscii == "abc\ndef".toSlice`
-/
def trimAscii (s : Slice) : Slice :=
  s.trimAsciiStart.trimAsciiEnd

/--
Checks whether {lean}`s1 == s2` if ASCII upper/lowercase are ignored.
-/
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

structure CharIterator where
  s : Slice
  currPos : s.Pos
  deriving Inhabited

/--
Creates and iterator over all characters (Unicode code points) in {name}`s`.
-/
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

/--
Creates and iterator over all characters (Unicode code points) in {name}`s`, starting from the end
of the slice and iterating towards the start.
-/
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

/--
Creates and iterator over all valid positions within {name}`s`.
-/
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

/--
Creates and iterator over all valid positions within {name}`s`, starting from the last valid
position and iterating towards the first one.
-/
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

/--
Creates and iterator over all bytes in {name}`s`.
-/
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

/--
Creates and iterator over all bytes in {name}`s`, starting from the last one and iterating towards
the first one.
-/
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

/--
Creates an iterator over all lines in {name}`s` with the line ending characters `\r\n` or `\n` being
stripped.
-/
def lines (s : Slice) :=
  s.splitInclusive '\n' |>.map lines.lineMap

end String.Slice
