/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving, Markus Himmel
-/
module

prelude
public import Init.Data.String.Pattern
public import Init.Data.Ord.Basic
public import Init.Data.Iterators.Combinators.FilterMap
public import Init.Data.String.ToSlice
public import Init.Data.String.Termination

set_option doc.verso true

/-!
This module defines the programming API for {name}`String.Slice`. The API mostly consists of
functionality for searching for various kinds of pattern matches in slices to iterate over them,
provide subslices according to matches etc. The key design principles behind this module are:
- Instead of providing one function per kind of pattern the API is generic over various kinds of
  patterns. Thus it only provides e.g. one kind of function for looking for the position of the
  first occurrence of a pattern. Currently the supported patterns are:
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

instance : HAppend String String.Slice String where
  -- This implementation performs an unnecessary copy which could be avoided by providing a custom
  -- C++ implementation for this instance. Note: if `String` had no custom runtime representation
  -- at all, then this would be very easy to get right from Lean using `ByteArray.copySlice`.
  hAppend s t := s ++ t.copy

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
    have h1 := by simp [h, String.Pos.Raw.le_iff]
    have h2 := by simp [h, String.Pos.Raw.le_iff]
    Internal.memcmpSlice s1 s2 s1.startPos.offset s2.startPos.offset s1.rawEndPos h1 h2
  else
    false

instance : BEq Slice where
  beq := beq

@[extern "lean_slice_hash"]
opaque hash (s : @& Slice) : UInt64

instance : Hashable Slice where
  hash := hash

instance : LT Slice where
  lt x y := x.copy < y.copy

@[extern "lean_slice_dec_lt"]
instance (x y : @& Slice) : Decidable (x < y) :=
  inferInstanceAs (Decidable (x.copy < y.copy))

instance : Ord Slice where
  compare x y := compareOfLessAndBEq x y

instance : LE Slice where
  le x y := ¬x < y

instance : DecidableLE Slice :=
  fun x y => inferInstanceAs (Decidable (¬x < y))

section ForwardPatternUsers

variable {ρ : Type} {σ : Slice → Type}
variable [∀ s, Std.Iterator (σ s) Id (SearchStep s)]
variable [∀ s, Std.Iterators.Finite (σ s) Id]
variable [∀ s, Std.IteratorLoop (σ s) Id Id]

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
def startsWith (s : Slice) (pat : ρ) [ForwardPattern pat] : Bool :=
  ForwardPattern.startsWith pat s

inductive SplitIterator {ρ : Type} (pat : ρ) (s : Slice) [ToForwardSearcher pat σ] where
  | operating (currPos : s.Pos) (searcher : Std.Iter (α := σ s) (SearchStep s))
  | atEnd
deriving Inhabited

namespace SplitIterator

variable {pat : ρ} [ToForwardSearcher pat σ]

inductive PlausibleStep

instance : Std.Iterator (SplitIterator pat s) Id Slice where
  IsPlausibleStep
    | ⟨.operating _ s⟩, .yield ⟨.operating _ s'⟩ _ => s'.IsPlausibleSuccessorOf s
    | ⟨.operating _ s⟩, .yield ⟨.atEnd ..⟩ _ => True
    | ⟨.operating _ s⟩, .skip ⟨.operating _ s'⟩ => s'.IsPlausibleSuccessorOf s
    | ⟨.operating _ s⟩, .skip ⟨.atEnd ..⟩ => False
    | ⟨.operating _ s⟩, .done => True
    | ⟨.atEnd⟩, .yield .. => False
    | ⟨.atEnd⟩, .skip _ => False
    | ⟨.atEnd⟩, .done => True
  step
    | ⟨.operating currPos searcher⟩ =>
      match h : searcher.step with
      | ⟨.yield searcher' (.matched startPos endPos), hps⟩ =>
        let slice := s.slice! currPos startPos
        let nextIt := ⟨.operating endPos searcher'⟩
        pure (.deflate ⟨.yield nextIt slice, by simp [nextIt, hps.isPlausibleSuccessor_of_yield]⟩)
      | ⟨.yield searcher' (.rejected ..), hps⟩ =>
        pure (.deflate ⟨.skip ⟨.operating currPos searcher'⟩,
          by simp [hps.isPlausibleSuccessor_of_yield]⟩)
      | ⟨.skip searcher', hps⟩ =>
        pure (.deflate ⟨.skip ⟨.operating currPos searcher'⟩,
          by simp [hps.isPlausibleSuccessor_of_skip]⟩)
      | ⟨.done, _⟩ =>
        let slice := s.sliceFrom currPos
        pure (.deflate ⟨.yield ⟨.atEnd⟩ slice, by simp⟩)
    | ⟨.atEnd⟩ => pure (.deflate ⟨.done, by simp⟩)

private def toOption : SplitIterator pat s → Option (Std.Iter (α := σ s) (SearchStep s))
  | .operating _ s => some s
  | .atEnd => none

private def finitenessRelation [Std.Iterators.Finite (σ s) Id] :
    Std.Iterators.FinitenessRelation (SplitIterator pat s) Id where
  Rel := InvImage (Option.lt Std.Iter.IsPlausibleSuccessorOf)
    (SplitIterator.toOption ∘ Std.IterM.internalState)
  wf := InvImage.wf _ (Option.wellFounded_lt Std.Iterators.Finite.wf_of_id)
  subrelation {it it'} h := by
    simp_wf
    obtain ⟨step, h, h'⟩ := h
    match step with
    | .yield it'' out | .skip it'' =>
      obtain rfl : it' = it'' := by simpa using h.symm
      simp only [Std.IterM.IsPlausibleStep, Std.Iterator.IsPlausibleStep] at h'
      revert h'
      match it, it' with
      | ⟨.operating _ searcher⟩, ⟨.operating _ searcher'⟩ => simp [SplitIterator.toOption, Option.lt]
      | ⟨.operating _ searcher⟩, ⟨.atEnd⟩ => simp [SplitIterator.toOption, Option.lt]
      | ⟨.atEnd⟩, _ => simp

@[no_expose]
instance [Std.Iterators.Finite (σ s) Id] : Std.Iterators.Finite (SplitIterator pat s) Id :=
  .of_finitenessRelation finitenessRelation

instance [Monad n] : Std.IteratorLoop (SplitIterator pat s) Id n :=
  .defaultImplementation

end SplitIterator

/--
Splits a slice at each subslice that matches the pattern {name}`pat`.

The subslices that matched the pattern are not included in any of the resulting subslices. If
multiple subslices in a row match the pattern, the resulting list will contain empty strings.

This function is generic over all currently supported patterns.

Examples:
 * {lean}`("coffee tea water".toSlice.split Char.isWhitespace).toList == ["coffee".toSlice, "tea".toSlice, "water".toSlice]`
 * {lean}`("coffee tea water".toSlice.split ' ').toList == ["coffee".toSlice, "tea".toSlice, "water".toSlice]`
 * {lean}`("coffee tea water".toSlice.split " tea ").toList == ["coffee".toSlice, "water".toSlice]`
 * {lean}`("ababababa".toSlice.split "aba").toList == ["coffee".toSlice, "water".toSlice]`
 * {lean}`("baaab".toSlice.split "aa").toList == ["b".toSlice, "ab".toSlice]`
-/
@[specialize pat]
def split (s : Slice) (pat : ρ) [ToForwardSearcher pat σ] : Std.Iter (α := SplitIterator pat s) Slice :=
  { internalState := .operating s.startPos (ToForwardSearcher.toSearcher pat s) }

inductive SplitInclusiveIterator {ρ : Type} (pat : ρ) (s : Slice) [ToForwardSearcher pat σ] where
  | operating (currPos : s.Pos) (searcher : Std.Iter (α := σ s) (SearchStep s))
  | atEnd
deriving Inhabited

namespace SplitInclusiveIterator

variable {pat : ρ} [ToForwardSearcher pat σ]

instance : Std.Iterator (SplitInclusiveIterator pat s) Id Slice where
  IsPlausibleStep
    | ⟨.operating _ s⟩, .yield ⟨.operating _ s'⟩ _ => s'.IsPlausibleSuccessorOf s
    | ⟨.operating _ s⟩, .yield ⟨.atEnd ..⟩ _ => True
    | ⟨.operating _ s⟩, .skip ⟨.operating _ s'⟩ => s'.IsPlausibleSuccessorOf s
    | ⟨.operating _ s⟩, .skip ⟨.atEnd ..⟩ => False
    | ⟨.operating _ s⟩, .done => True
    | ⟨.atEnd⟩, .yield .. => False
    | ⟨.atEnd⟩, .skip _ => False
    | ⟨.atEnd⟩, .done => True
  step
    | ⟨.operating currPos searcher⟩ =>
      match h : searcher.step with
      | ⟨.yield searcher' (.matched _ endPos), hps⟩ =>
        let slice := s.slice! currPos endPos
        let nextIt := ⟨.operating endPos searcher'⟩
        pure (.deflate ⟨.yield nextIt slice,
          by simp [nextIt, hps.isPlausibleSuccessor_of_yield]⟩)
      | ⟨.yield searcher' (.rejected ..), hps⟩ =>
        pure (.deflate ⟨.skip ⟨.operating currPos searcher'⟩,
          by simp [hps.isPlausibleSuccessor_of_yield]⟩)
      | ⟨.skip searcher', hps⟩ =>
        pure (.deflate ⟨.skip ⟨.operating currPos searcher'⟩,
          by simp [hps.isPlausibleSuccessor_of_skip]⟩)
      | ⟨.done, _⟩ =>
        if currPos != s.endPos then
          let slice := s.sliceFrom currPos
          pure (.deflate ⟨.yield ⟨.atEnd⟩ slice, by simp⟩)
        else
          pure (.deflate ⟨.done, by simp⟩)
    | ⟨.atEnd⟩ => pure (.deflate ⟨.done, by simp⟩)

private def toOption : SplitInclusiveIterator pat s → Option (Std.Iter (α := σ s) (SearchStep s))
  | .operating _ s => some s
  | .atEnd => none

private def finitenessRelation [Std.Iterators.Finite (σ s) Id] :
    Std.Iterators.FinitenessRelation (SplitInclusiveIterator pat s) Id where
  Rel := InvImage (Option.lt Std.Iter.IsPlausibleSuccessorOf)
    (SplitInclusiveIterator.toOption ∘ Std.IterM.internalState)
  wf := InvImage.wf _ (Option.wellFounded_lt Std.Iterators.Finite.wf_of_id)
  subrelation {it it'} h := by
    simp_wf
    obtain ⟨step, h, h'⟩ := h
    match step with
    | .yield it'' out | .skip it'' =>
      obtain rfl : it' = it'' := by simpa using h.symm
      simp only [Std.IterM.IsPlausibleStep, Std.Iterator.IsPlausibleStep] at h'
      revert h'
      match it, it' with
      | ⟨.operating _ searcher⟩, ⟨.operating _ searcher'⟩ => simp [SplitInclusiveIterator.toOption, Option.lt]
      | ⟨.operating _ searcher⟩, ⟨.atEnd⟩ => simp [SplitInclusiveIterator.toOption, Option.lt]
      | ⟨.atEnd⟩, _ => simp

@[no_expose]
instance [Std.Iterators.Finite (σ s) Id] :
    Std.Iterators.Finite (SplitInclusiveIterator pat s) Id :=
  .of_finitenessRelation finitenessRelation

instance [Monad n] {s} :
    Std.IteratorLoop (SplitInclusiveIterator pat s) Id n :=
  .defaultImplementation

end SplitInclusiveIterator

/--
Splits a slice at each subslice that matches the pattern {name}`pat`. Unlike {name}`split` the
matched subslices are included at the end of each subslice.

This function is generic over all currently supported patterns.

Examples:
 * {lean}`("coffee tea water".toSlice.splitInclusive Char.isWhitespace).toList == ["coffee ".toSlice, "tea ".toSlice, "water".toSlice]`
 * {lean}`("coffee tea water".toSlice.splitInclusive ' ').toList == ["coffee ".toSlice, "tea ".toSlice, "water".toSlice]`
 * {lean}`("coffee tea water".toSlice.splitInclusive " tea ").toList == ["coffee tea ".toSlice, "water".toSlice]`
 * {lean}`("baaab".toSlice.splitInclusive "aa").toList == ["baa".toSlice, "ab".toSlice]`
-/
@[specialize pat]
def splitInclusive (s : Slice) (pat : ρ) [ToForwardSearcher pat σ] :
    Std.Iter (α := SplitInclusiveIterator pat s) Slice :=
  { internalState := .operating s.startPos (ToForwardSearcher.toSearcher pat s) }

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
def dropPrefix? (s : Slice) (pat : ρ) [ForwardPattern pat] : Option Slice :=
  (ForwardPattern.dropPrefix? pat s).map s.sliceFrom

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
def dropPrefix (s : Slice) (pat : ρ) [ForwardPattern pat] : Slice :=
  dropPrefix? s pat |>.getD s

/--
Constructs a new string obtained by replacing all occurrences of {name}`pattern` with
{name}`replacement` in {name}`s`.

This function is generic over all currently supported patterns. The replacement may be a
{name}`String` or a {name}`String.Slice`.

Examples:
* {lean}`"red green blue".toSlice.replace 'e' "" = "rd grn blu"`
* {lean}`"red green blue".toSlice.replace (fun c => c == 'u' || c == 'e') "" = "rd grn bl"`
* {lean}`"red green blue".toSlice.replace "e" "" = "rd grn blu"`
* {lean}`"red green blue".toSlice.replace "ee" "E" = "red grEn blue"`
* {lean}`"red green blue".toSlice.replace "e" "E" = "rEd grEEn bluE"`
* {lean}`"aaaaa".toSlice.replace "aa" "b" = "bba"`
* {lean}`"abc".toSlice.replace "" "k" = "kakbkck"`
-/
def replace [ToSlice α] (s : Slice) (pattern : ρ) [ToForwardSearcher pattern σ] (replacement : α) :
    String :=
  (ToForwardSearcher.toSearcher pattern s).fold (init := "") (fun
    | sofar, .matched .. => sofar ++ ToSlice.toSlice replacement
    | sofar, .rejected start stop => sofar ++ s.slice! start stop)

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
  s.sliceFrom (s.startPos.nextn n)

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
def dropWhile (s : Slice) (pat : ρ) [ForwardPattern pat] : Slice :=
  go s.startPos
where
  @[specialize pat]
  go (curr : s.Pos) : Slice :=
    if let some nextCurr := ForwardPattern.dropPrefix? pat (s.sliceFrom curr) then
      if curr < Pos.ofSliceFrom nextCurr then
        go (Pos.ofSliceFrom nextCurr)
      else
        s.sliceFrom curr
    else
      s.sliceFrom curr
  termination_by curr

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
  s.sliceTo (s.startPos.nextn n)

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
def takeWhile (s : Slice) (pat : ρ) [ForwardPattern pat] : Slice :=
  go s.startPos
where
  @[specialize pat]
  go (curr : s.Pos) : Slice :=
    if let some nextCurr := ForwardPattern.dropPrefix? pat (s.sliceFrom curr) then
      if curr < Pos.ofSliceFrom nextCurr then
        go (Pos.ofSliceFrom nextCurr)
      else
        s.sliceTo curr
    else
      s.sliceTo curr
  termination_by curr

/--
Finds the position of the first match of the pattern {name}`pat` in a slice {name}`s`. If there
is no match {name}`none` is returned.

This function is generic over all currently supported patterns.

Examples:
 * {lean}`("coffee tea water".toSlice.find? Char.isWhitespace).map (·.get!) == some ' '`
 * {lean}`"tea".toSlice.find? (fun (c : Char) => c == 'X') == none`
 * {lean}`("coffee tea water".toSlice.find? "tea").map (·.get!) == some 't'`
-/
@[inline]
def find? (s : Slice) (pat : ρ) [ToForwardSearcher pat σ] : Option s.Pos :=
  let searcher := ToForwardSearcher.toSearcher pat s
  searcher.findSome? (fun | .matched startPos _ => some startPos | .rejected .. => none)

/--
Finds the position of the first match of the pattern {name}`pat` in a slice {name}`s`. If there
is no match {lean}`s.endPos` is returned.

This function is generic over all currently supported patterns.

Examples:
 * {lean}`("coffee tea water".toSlice.find Char.isWhitespace).get! == ' '`
 * {lean}`"tea".toSlice.find (fun (c : Char) => c == 'X') == "tea".toSlice.endPos`
 * {lean}`("coffee tea water".toSlice.find "tea").get! == 't'`
-/
@[inline]
def find (s : Slice) (pat : ρ) [ToForwardSearcher pat σ] : s.Pos :=
  s.find? pat |>.getD s.endPos

/--
Checks whether a slice has a match of the pattern {name}`pat` anywhere.

This function is generic over all currently supported patterns.

Examples:
 * {lean}`"coffee tea water".toSlice.contains Char.isWhitespace = true`
 * {lean}`"tea".toSlice.contains (fun (c : Char) => c == 'X') = false`
 * {lean}`"coffee tea water".toSlice.contains "tea" = true`
-/
@[specialize pat, suggest_for String.Slice.some]
def contains (s : Slice) (pat : ρ) [ToForwardSearcher pat σ] : Bool :=
  let searcher := ToForwardSearcher.toSearcher pat s
  searcher.any (· matches .matched ..)

@[inline, inherit_doc contains]
def any (s : Slice) (pat : ρ) [ToForwardSearcher pat σ] : Bool :=
  s.contains pat

/--
Checks whether a slice only consists of matches of the pattern {name}`pat`.

Short-circuits at the first pattern mis-match.

This function is generic over all currently supported patterns.

Examples:
 * {lean}`"brown".toSlice.all Char.isLower = true`
 * {lean}`"brown and orange".toSlice.all Char.isLower = false`
 * {lean}`"aaaaaa".toSlice.all 'a' = true`
 * {lean}`"aaaaaa".toSlice.all "aa" = true`
 * {lean}`"aaaaaaa".toSlice.all "aa" = false`
-/
@[inline]
def all (s : Slice) (pat : ρ) [ForwardPattern pat] : Bool :=
  s.dropWhile pat |>.isEmpty

end ForwardPatternUsers

section BackwardPatternUsers

variable {σ : Slice → Type}
variable [∀ s, Std.Iterator (σ s) Id (SearchStep s)]
variable [∀ s, Std.Iterators.Finite (σ s) Id]
variable [∀ s, Std.IteratorLoop (σ s) Id Id]

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
def endsWith (s : Slice) (pat : ρ) [BackwardPattern pat]  : Bool :=
  BackwardPattern.endsWith pat s

inductive RevSplitIterator {ρ : Type} (pat : ρ) (s : Slice) [ToBackwardSearcher pat σ] where
  | operating (currPos : s.Pos) (searcher : Std.Iter (α := σ s) (SearchStep s))
  | atEnd
deriving Inhabited

namespace RevSplitIterator

variable [ToBackwardSearcher ρ σ]

instance [Pure m] : Std.Iterator (RevSplitIterator ρ s) m Slice where
  IsPlausibleStep
    | ⟨.operating _ s⟩, .yield ⟨.operating _ s'⟩ _ => s'.IsPlausibleSuccessorOf s
    | ⟨.operating _ s⟩, .yield ⟨.atEnd ..⟩ _ => True
    | ⟨.operating _ s⟩, .skip ⟨.operating _ s'⟩ => s'.IsPlausibleSuccessorOf s
    | ⟨.operating _ s⟩, .skip ⟨.atEnd ..⟩ => False
    | ⟨.operating _ s⟩, .done => True
    | ⟨.atEnd⟩, .yield .. => False
    | ⟨.atEnd⟩, .skip _ => False
    | ⟨.atEnd⟩, .done => True
  step
    | ⟨.operating currPos searcher⟩ =>
      match h : searcher.step with
      | ⟨.yield searcher' (.matched startPos endPos), hps⟩ =>
        let slice := s.slice! endPos currPos
        let nextIt := ⟨.operating startPos searcher'⟩
        pure (.deflate ⟨.yield nextIt slice, by simp [nextIt, hps.isPlausibleSuccessor_of_yield]⟩)
      | ⟨.yield searcher' (.rejected ..), hps⟩ =>
        pure (.deflate ⟨.skip ⟨.operating currPos searcher'⟩,
          by simp [hps.isPlausibleSuccessor_of_yield]⟩)
      | ⟨.skip searcher', hps⟩ =>
        pure (.deflate ⟨.skip ⟨.operating currPos searcher'⟩,
          by simp [hps.isPlausibleSuccessor_of_skip]⟩)
      | ⟨.done, _⟩ =>
        if currPos ≠ s.startPos then
          let slice := s.sliceTo currPos
          pure (.deflate ⟨.yield ⟨.atEnd⟩ slice, by simp⟩)
        else
          pure (.deflate ⟨.done, by simp⟩)
    | ⟨.atEnd⟩ => pure (.deflate ⟨.done, by simp⟩)

private def toOption : RevSplitIterator ρ s → Option (Std.Iter (α := σ s) (SearchStep s))
  | .operating _ s => some s
  | .atEnd => none

private def finitenessRelation [Std.Iterators.Finite (σ s) Id] :
    Std.Iterators.FinitenessRelation (RevSplitIterator ρ s) Id where
  Rel := InvImage (Option.lt Std.Iter.IsPlausibleSuccessorOf)
    (RevSplitIterator.toOption ∘ Std.IterM.internalState)
  wf := InvImage.wf _ (Option.wellFounded_lt Std.Iterators.Finite.wf_of_id)
  subrelation {it it'} h := by
    simp_wf
    obtain ⟨step, h, h'⟩ := h
    match step with
    | .yield it'' out | .skip it'' =>
      obtain rfl : it' = it'' := by simpa using h.symm
      simp only [Std.IterM.IsPlausibleStep, Std.Iterator.IsPlausibleStep] at h'
      revert h'
      match it, it' with
      | ⟨.operating _ searcher⟩, ⟨.operating _ searcher'⟩ => simp [RevSplitIterator.toOption, Option.lt]
      | ⟨.operating _ searcher⟩, ⟨.atEnd⟩ => simp [RevSplitIterator.toOption, Option.lt]
      | ⟨.atEnd⟩, _ => simp

@[no_expose]
instance [Std.Iterators.Finite (σ s) Id] : Std.Iterators.Finite (RevSplitIterator ρ s) Id :=
  .of_finitenessRelation finitenessRelation

instance [Monad m] [Monad n] : Std.IteratorLoop (RevSplitIterator ρ s) m n :=
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
 * {lean}`("coffee tea water".toSlice.revSplit Char.isWhitespace).toList == ["water".toSlice, "tea".toSlice, "coffee".toSlice]`
 * {lean}`("coffee tea water".toSlice.revSplit ' ').toList == ["water".toSlice, "tea".toSlice, "coffee".toSlice]`
-/
@[specialize pat]
def revSplit (s : Slice) (pat : ρ) [ToBackwardSearcher pat σ] :
    Std.Iter (α := RevSplitIterator pat s) Slice :=
  { internalState := .operating s.endPos (ToBackwardSearcher.toSearcher pat s) }

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
def dropSuffix? (s : Slice) (pat : ρ) [BackwardPattern pat] : Option Slice :=
  (BackwardPattern.dropSuffix? pat s).map s.sliceTo

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
def dropSuffix (s : Slice) (pat : ρ) [BackwardPattern pat]  : Slice :=
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
  s.sliceTo (s.endPos.prevn n)

/--
Creates a new slice that contains the longest suffix of {name}`s` for which {name}`pat` matched
(potentially repeatedly).

Examples:
 * {lean}`"red green blue".toSlice.dropEndWhile Char.isLower == "red green ".toSlice`
 * {lean}`"red green blue".toSlice.dropEndWhile 'e' == "red green blu".toSlice`
 * {lean}`"red green blue".toSlice.dropEndWhile (fun (_ : Char) => true) == "".toSlice`
-/
@[inline]
def dropEndWhile (s : Slice) (pat : ρ) [BackwardPattern pat] : Slice :=
  go s.endPos
where
  @[specialize pat]
  go (curr : s.Pos) : Slice :=
    if let some nextCurr := BackwardPattern.dropSuffix? pat (s.sliceTo curr) then
      if Pos.ofSliceTo nextCurr < curr then
        go (Pos.ofSliceTo nextCurr)
      else
        s.sliceTo curr
    else
      s.sliceTo curr
  termination_by curr.down

/--
Removes trailing whitespace from a slice by moving its end position to the last non-whitespace
character, or to its start position if there is no non-whitespace character.

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
  s.sliceFrom (s.endPos.prevn n)

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
def takeEndWhile (s : Slice) (pat : ρ) [BackwardPattern pat] : Slice :=
  go s.endPos
where
  @[specialize pat]
  go (curr : s.Pos) : Slice :=
    if let some nextCurr := BackwardPattern.dropSuffix? pat (s.sliceTo curr) then
      if Pos.ofSliceTo nextCurr < curr then
        go (Pos.ofSliceTo nextCurr)
      else
        s.sliceFrom curr
    else
      s.sliceFrom curr
  termination_by curr.down

/--
Finds the position of the first match of the pattern {name}`pat` in a slice, starting
from the end of the slice and traversing towards the start. If there is no match {name}`none` is
returned.

This function is generic over all currently supported patterns except
{name}`String`/{name}`String.Slice`.

Examples:
 * {lean}`("coffee tea water".toSlice.revFind? Char.isWhitespace).map (·.get!) == some ' '`
 * {lean}`"tea".toSlice.revFind? (fun (c : Char) => c == 'X') == none`
-/
@[specialize pat]
def revFind? (s : Slice) (pat : ρ) [ToBackwardSearcher pat σ] : Option s.Pos :=
  let searcher := ToBackwardSearcher.toSearcher pat s
  searcher.findSome? (fun | .matched startPos _ => some startPos | .rejected .. => none)

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
  go (s1 : Slice) (s1Curr : String.Pos.Raw) (s2 : Slice) (s2Curr : String.Pos.Raw) : Bool :=
    if h : s1Curr < s1.rawEndPos ∧ s2Curr < s2.rawEndPos then
      let c1 := (s1.getUTF8Byte s1Curr h.left).toAsciiLower
      let c2 := (s2.getUTF8Byte s2Curr h.right).toAsciiLower
      if c1 == c2 then
        go s1 s1Curr.inc s2 s2Curr.inc
      else
        false
    else
      s1Curr == s1.rawEndPos && s2Curr == s2.rawEndPos
  termination_by s1.endPos.offset.byteIdx - s1Curr.byteIdx
  decreasing_by
    simp [String.Pos.Raw.lt_iff] at h ⊢
    omega

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

@[deprecated "There is no constant-time length function on slices. Use `s.positions.count` instead, or `isEmpty` if you only need to know whether the slice is empty." (since := "2025-11-20")]
def length (s : Slice) : Nat :=
  s.positions.count

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

Examples:
 * {lean}`"foo\r\nbar\n\nbaz\n".toSlice.lines.toList  == ["foo".toSlice, "bar".toSlice, "".toSlice, "baz".toSlice]`
 * {lean}`"foo\r\nbar\n\nbaz".toSlice.lines.toList  == ["foo".toSlice, "bar".toSlice, "".toSlice, "baz".toSlice]`
 * {lean}`"foo\r\nbar\n\nbaz\r".toSlice.lines.toList  == ["foo".toSlice, "bar".toSlice, "".toSlice, "baz\r".toSlice]`
-/
def lines (s : Slice) :=
  s.splitInclusive '\n' |>.map lines.lineMap

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

/--
Checks whether the slice can be interpreted as the decimal representation of a natural number.

A slice can be interpreted as a decimal natural number if it is not empty and all the characters in
it are digits. Underscores ({lit}`_`) are allowed as digit separators for readability, but cannot appear
at the start, at the end, or consecutively.

Use {name (scope := "Init.Data.String.Slice")}`toNat?` or
{name (scope := "Init.Data.String.Slice")}`toNat!` to convert such a slice to a natural number.

Examples:
 * {lean}`"".toSlice.isNat = false`
 * {lean}`"0".toSlice.isNat = true`
 * {lean}`"5".toSlice.isNat = true`
 * {lean}`"05".toSlice.isNat = true`
 * {lean}`"587".toSlice.isNat = true`
 * {lean}`"1_000".toSlice.isNat = true`
 * {lean}`"100_000_000".toSlice.isNat = true`
 * {lean}`"-587".toSlice.isNat = false`
 * {lean}`" 5".toSlice.isNat = false`
 * {lean}`"2+3".toSlice.isNat = false`
 * {lean}`"0xff".toSlice.isNat = false`
 * {lean}`"_123".toSlice.isNat = false`
 * {lean}`"123_".toSlice.isNat = false`
 * {lean}`"12__34".toSlice.isNat = false`
-/
@[inline]
def isNat (s : Slice) : Bool :=
  if s.isEmpty then
    false
  else
    -- Track: isFirst, lastWasUnderscore, lastCharWasDigit, valid
    let result := s.foldl (fun (isFirst, lastWasUnderscore, _lastCharWasDigit, valid) c =>
      let isDigit := c.isDigit
      let isUnderscore := c = '_'
      let newValid := valid && (isDigit || isUnderscore) &&
                      !(isFirst && isUnderscore) &&  -- Cannot start with underscore
                      !(lastWasUnderscore && isUnderscore)  -- No consecutive underscores
      (false, isUnderscore, isDigit, newValid))
      (true, false, false, true)
    -- Must be valid and last character must have been a digit (not underscore)
    result.2.2.2 && result.2.2.1

/--
Interprets a slice as the decimal representation of a natural number, returning it. Returns
{name}`none` if the slice does not contain a decimal natural number.

A slice can be interpreted as a decimal natural number if it is not empty and all the characters in
it are digits. Underscores ({lit}`_`) are allowed as digit separators and are ignored during parsing.

Use {name}`isNat` to check whether {name}`toNat?` would return {name}`some`.
{name (scope := "Init.Data.String.Slice")}`toNat!` is an alternative that panics instead of
returning {name}`none` when the slice is not a natural number.

Examples:
 * {lean}`"".toSlice.toNat? = none`
 * {lean}`"0".toSlice.toNat? = some 0`
 * {lean}`"5".toSlice.toNat? = some 5`
 * {lean}`"587".toSlice.toNat? = some 587`
 * {lean}`"1_000".toSlice.toNat? = some 1000`
 * {lean}`"100_000_000".toSlice.toNat? = some 100000000`
 * {lean}`"-587".toSlice.toNat? = none`
 * {lean}`" 5".toSlice.toNat? = none`
 * {lean}`"2+3".toSlice.toNat? = none`
 * {lean}`"0xff".toSlice.toNat? = none`
-/
def toNat? (s : Slice) : Option Nat :=
  if s.isNat then
    some <| s.foldl (fun n c => if c = '_' then n else n * 10 + (c.toNat - '0'.toNat)) 0
  else
    none

/--
Interprets a slice as the decimal representation of a natural number, returning it. Panics if the
slice does not contain a decimal natural number.

A slice can be interpreted as a decimal natural number if it is not empty and all the characters in
it are digits. Underscores ({lit}`_`) are allowed as digit separators and are ignored during parsing.

Use {name}`isNat` to check whether {name}`toNat!` would return a value. {name}`toNat?` is a safer
alternative that returns {name}`none` instead of panicking when the string is not a natural number.

Examples:
 * {lean}`"0".toSlice.toNat! = 0`
 * {lean}`"5".toSlice.toNat! = 5`
 * {lean}`"587".toSlice.toNat! = 587`
 * {lean}`"1_000".toSlice.toNat! = 1000`
-/
def toNat! (s : Slice) : Nat :=
  if s.isNat then
    s.foldl (fun n c => if c = '_' then n else n * 10 + (c.toNat - '0'.toNat)) 0
  else
    panic! "Nat expected"

/--
Returns the first character in {name}`s`. If {name}`s` is empty, returns {name}`none`.

Examples:
* {lean}`"abc".toSlice.front? = some 'a'`
* {lean}`"".toSlice.front? = none`
-/
@[inline, expose]
def front? (s : Slice) : Option Char :=
  s.startPos.get?

/--
Returns the first character in {name}`s`. If {name}`s` is empty, returns {lean}`(default : Char)`.

Examples:
* {lean}`"abc".toSlice.front = 'a'`
* {lean}`"".toSlice.front = (default : Char)`
-/
@[inline, expose]
def front (s : Slice) : Char :=
  s.front?.getD default

/--
Checks whether the slice can be interpreted as the decimal representation of an integer.

A slice can be interpreted as a decimal integer if it only consists of at least one decimal digit
and optionally {lit}`-` in front. Leading {lit}`+` characters are not allowed.

Use {name (scope := "Init.Data.String.Slice")}`String.Slice.toInt?` or {name (scope := "Init.Data.String.Slice")}`String.toInt!` to convert such a string to an integer.

Examples:
 * {lean}`"".toSlice.isInt = false`
 * {lean}`"-".toSlice.isInt = false`
 * {lean}`"0".toSlice.isInt = true`
 * {lean}`"-0".toSlice.isInt = true`
 * {lean}`"5".toSlice.isInt = true`
 * {lean}`"587".toSlice.isInt = true`
 * {lean}`"-587".toSlice.isInt = true`
 * {lean}`"+587".toSlice.isInt = false`
 * {lean}`" 5".toSlice.isInt = false`
 * {lean}`"2-3".toSlice.isInt = false`
 * {lean}`"0xff".toSlice.isInt = false`
-/
def isInt (s : Slice) : Bool :=
  if s.front = '-' then
    (s.drop 1).isNat
  else
    s.isNat

/--
Interprets a slice as the decimal representation of an integer, returning it. Returns {lean}`none` if
the string does not contain a decimal integer.

A string can be interpreted as a decimal integer if it only consists of at least one decimal digit
and optionally {lit}`-` in front. Leading {lit}`+` characters are not allowed.

Use {name}`Slice.isInt` to check whether {name}`Slice.toInt?` would return {lean}`some`.
{name (scope := "Init.Data.String.Slice")}`Slice.toInt!` is an alternative that panics instead of
returning {lean}`none` when the string is not an integer.

Examples:
 * {lean}`"".toSlice.toInt? = none`
 * {lean}`"-".toSlice.toInt? = none`
 * {lean}`"0".toSlice.toInt? = some 0`
 * {lean}`"5".toSlice.toInt? = some 5`
 * {lean}`"-5".toSlice.toInt? = some (-5)`
 * {lean}`"587".toSlice.toInt? = some 587`
 * {lean}`"-587".toSlice.toInt? = some (-587)`
 * {lean}`" 5".toSlice.toInt? = none`
 * {lean}`"2-3".toSlice.toInt? = none`
 * {lean}`"0xff".toSlice.toInt? = none`
-/
def toInt? (s : Slice) : Option Int :=
  if s.front = '-' then
    Int.negOfNat <$> (s.drop 1).toNat?
  else
   Int.ofNat <$> s.toNat?

/--
Interprets a string as the decimal representation of an integer, returning it. Panics if the string
does not contain a decimal integer.

A string can be interpreted as a decimal integer if it only consists of at least one decimal digit
and optionally {lit}`-` in front. Leading `+` characters are not allowed.

Use {name}`Slice.isInt` to check whether {name}`Slice.toInt!` would return a value.
{name}`Slice.toInt?` is a safer alternative that returns {lean}`none` instead of panicking when the
string is not an integer.

Examples:
 * {lean}`"0".toSlice.toInt! = 0`
 * {lean}`"5".toSlice.toInt! = 5`
 * {lean}`"587".toSlice.toInt! = 587`
 * {lean}`"-587".toSlice.toInt! = -587`
-/
@[inline]
def toInt! (s : Slice) : Int :=
  match s.toInt? with
  | some v => v
  | none   => panic "Int expected"

/--
Returns the last character in {name}`s`. If {name}`s` is empty, returns {name}`none`.

Examples:
* {lean}`"abc".toSlice.back? = some 'c'`
* {lean}`"".toSlice.back? = none`
-/
@[inline, expose]
def back? (s : Slice) : Option Char :=
  s.endPos.prev? |>.bind (·.get?)

/--
Returns the last character in {name}`s`. If {name}`s` is empty, returns {lean}`(default : Char)`.

Examples:
* {lean}`"abc".toSlice.back = 'c'`
* {lean}`"".toSlice.back = (default : Char)`
-/
@[inline, expose]
def back (s : Slice) : Char :=
  s.back?.getD default

/--
Appends the slices in a list of slices, placing the separator {name}`s` between each pair.

Examples:
 * {lean}`", ".toSlice.intercalate ["red".toSlice, "green".toSlice, "blue".toSlice] = "red, green, blue"`
 * {lean}`" and ".toSlice.intercalate ["tea".toSlice, "coffee".toSlice] = "tea and coffee"`
 * {lean}`" | ".toSlice.intercalate ["M".toSlice, "".toSlice, "N".toSlice] = "M |  | N"`
-/
def intercalate (s : Slice) : List Slice → String
  | []      => ""
  | a :: as => go a.copy s as
where go (acc : String) (s : Slice) : List Slice → String
  | a :: as => go (acc ++ s ++ a) s as
  | []      => acc

@[inherit_doc Slice.copy]
def toString (s : Slice) : String :=
  s.copy

instance : ToString String.Slice where
  toString := toString

/--
Converts a string to the Lean compiler's representation of names. The resulting name is
hierarchical, and the string is split at the dots ({lean}`'.'`).

{lean}`"a.b".toSlice.toName` is the name {lit}`a.b`, not {lit}`«a.b»`. For the latter, use
`Name.mkSimple`.
-/
def toName (s : Slice) : Lean.Name :=
  s.toString.toName

instance : Std.ToFormat String.Slice where
  format s := Std.ToFormat.format s.copy

end String.Slice

/-- Converts a {lean}`Std.Iter String.Slice` to a {lean}`List String`. -/
@[inline]
def Std.Iter.toStringList {α : Type} [Std.Iterator α Id String.Slice]
    [Std.Iterators.Finite α Id]
    (i : Std.Iter (α := α) String.Slice) : List String :=
  i.map String.Slice.copy |>.toList

/-- Converts a {lean}`Std.Iter String.Slice` to an {lean}`Array String`. -/
def Std.Iter.toStringArray {α : Type} [Std.Iterator α Id String.Slice]
    [Std.Iterators.Finite α Id]
    (i : Std.Iter (α := α) String.Slice) : Array String :=
  i.map String.Slice.copy |>.toArray
