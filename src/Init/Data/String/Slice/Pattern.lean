/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving, Markus Himmel
-/
module

prelude
public import Init.Data.String.Slice.Basic
public import Init.Data.String.Pattern
public import Init.Data.String.ToSlice
public import Init.Data.String.Subslice
public import Init.Data.Iterators.Combinators.FilterMap
public import Init.Data.String.Iter.Basic
import Init.Data.Iterators.Consumers.Collect
import Init.Data.Iterators.Consumers.Loop
import Init.Data.Option.Lemmas
import Init.Data.String.Termination

set_option doc.verso true

public section

namespace String.Slice

open Pattern

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

instance : Std.Iterator (SplitIterator pat s) Id s.Subslice where
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
        let slice := s.subslice! currPos startPos
        let nextIt := ⟨.operating endPos searcher'⟩
        pure (.deflate ⟨.yield nextIt slice, by simp [nextIt, hps.isPlausibleSuccessor_of_yield]⟩)
      | ⟨.yield searcher' (.rejected ..), hps⟩ =>
        pure (.deflate ⟨.skip ⟨.operating currPos searcher'⟩,
          by simp [hps.isPlausibleSuccessor_of_yield]⟩)
      | ⟨.skip searcher', hps⟩ =>
        pure (.deflate ⟨.skip ⟨.operating currPos searcher'⟩,
          by simp [hps.isPlausibleSuccessor_of_skip]⟩)
      | ⟨.done, _⟩ =>
        let slice := s.subsliceFrom currPos
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
      simp only [Std.IterM.IsPlausibleStep, Std.Iterator.IsPlausibleStep, instIteratorIdSubslice] at h' -- TODO
      revert h'
      match it, it' with
      | ⟨.operating _ searcher⟩, ⟨.operating _ searcher'⟩ => simp [SplitIterator.toOption, Option.lt]
      | ⟨.operating _ searcher⟩, ⟨.atEnd⟩ => simp [SplitIterator.toOption, Option.lt]
      | ⟨.atEnd⟩, _ => simp

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
 * {lean}`("coffee tea water".toSlice.splitToSubslice Char.isWhitespace).toStringList == ["coffee", "tea", "water"]`
 * {lean}`("coffee tea water".toSlice.splitToSubslice ' ').toStringList == ["coffee", "tea", "water"]`
 * {lean}`("coffee tea water".toSlice.splitToSubslice " tea ").toStringList == ["coffee", "water"]`
 * {lean}`("ababababa".toSlice.splitToSubslice "aba").toStringList == ["coffee", "water"]`
 * {lean}`("baaab".toSlice.splitToSubslice "aa").toStringList == ["b", "ab"]`
-/
@[specialize pat, cbv_opaque]
def splitToSubslice (s : Slice) (pat : ρ) [ToForwardSearcher pat σ] :
    Std.Iter (α := SplitIterator pat s) s.Subslice :=
  { internalState := .operating s.startPos (ToForwardSearcher.toSearcher pat s) }

/--
Splits a slice at each subslice that matches the pattern {name}`pat`.

The subslices that matched the pattern are not included in any of the resulting subslices. If
multiple subslices in a row match the pattern, the resulting list will contain empty strings.

This function is generic over all currently supported patterns.

Examples:
 * {lean}`("coffee tea water".toSlice.split Char.isWhitespace).toStringList == ["coffee", "tea", "water"]`
 * {lean}`("coffee tea water".toSlice.split ' ').toStringList == ["coffee", "tea", "water"]`
 * {lean}`("coffee tea water".toSlice.split " tea ").toStringList == ["coffee", "water"]`
 * {lean}`("ababababa".toSlice.split "aba").toStringList == ["coffee", "water"]`
 * {lean}`("baaab".toSlice.split "aa").toStringList == ["b", "ab"]`
-/
@[inline]
def split (s : Slice) (pat : ρ) [ToForwardSearcher pat σ] :=
  (s.splitToSubslice pat |>.map Subslice.toSlice : Std.Iter Slice)

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
      simp only [Std.IterM.IsPlausibleStep, Std.Iterator.IsPlausibleStep, instIteratorId] at h' -- TODO
      revert h'
      match it, it' with
      | ⟨.operating _ searcher⟩, ⟨.operating _ searcher'⟩ => simp [SplitInclusiveIterator.toOption, Option.lt]
      | ⟨.operating _ searcher⟩, ⟨.atEnd⟩ => simp [SplitInclusiveIterator.toOption, Option.lt]
      | ⟨.atEnd⟩, _ => simp

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
If {name}`pat` matches a prefix of {name}`s`, returns the position at the start of the remainder.
Returns {name}`none` otherwise.

This function is generic over all currently supported patterns.
-/
@[inline]
def skipPrefix? (s : Slice) (pat : ρ) [ForwardPattern pat] : Option s.Pos :=
  ForwardPattern.skipPrefix? pat s

/--
If {name}`pat` matches a prefix at {name}`pos`, returns the position after the end of the match.
Returns {name}`none` otherwise.

This function is generic over all currently supported patterns.
-/
@[inline]
def Pos.skip? {s : Slice} (pos : s.Pos) (pat : ρ) [ForwardPattern pat] : Option s.Pos :=
  ((s.sliceFrom pos).skipPrefix? pat).map Pos.ofSliceFrom

/--
If {name}`pat` matches a prefix of {name}`s`, returns the remainder. Returns {name}`none` otherwise.

Use {name (scope := "Init.Data.String.Slice.Pattern")}`String.Slice.dropPrefix` to return the slice
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
  (s.skipPrefix? pat).map s.sliceFrom

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
Advances {name}`pos` as long as {name}`pat` matches.
-/
@[specialize pat]
def Pos.skipWhile {s : Slice} (pos : s.Pos) (pat : ρ) [ForwardPattern pat] : s.Pos :=
  match pos.skip? pat with
  | some nextCurr =>
    if pos < nextCurr then
      skipWhile nextCurr pat
    else
      pos
  | none => pos
termination_by pos

/--
Returns the position after the longest prefix of {name}`s` for which {name}`pat` matches
(potentially repeatedly).
-/
@[inline]
def skipPrefixWhile (s : Slice) (pat : ρ) [ForwardPattern pat] : s.Pos :=
  s.startPos.skipWhile pat

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
  s.sliceFrom (s.skipPrefixWhile pat)

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
  s.sliceTo (s.skipPrefixWhile pat)

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
  s.skipPrefixWhile pat == s.endPos

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
      simp only [Std.IterM.IsPlausibleStep, Std.Iterator.IsPlausibleStep, instIteratorOfPure] at h' -- TODO
      revert h'
      match it, it' with
      | ⟨.operating _ searcher⟩, ⟨.operating _ searcher'⟩ => simp [RevSplitIterator.toOption, Option.lt]
      | ⟨.operating _ searcher⟩, ⟨.atEnd⟩ => simp [RevSplitIterator.toOption, Option.lt]
      | ⟨.atEnd⟩, _ => simp

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
If {name}`pat` matches a suffix of {name}`s`, returns the position at the beginning of the suffix.
Returns {name}`none` otherwise.

This function is generic over all currently supported patterns.
-/
@[inline]
def skipSuffix? (s : Slice) (pat : ρ) [BackwardPattern pat] : Option s.Pos :=
  BackwardPattern.skipSuffix? pat s

/--
If {name}`pat` matches a suffix at {name}`pos`, returns the position at the beginning of the match.
Returns {name}`none` otherwise.

This function is generic over all currently supported patterns.
-/
@[inline]
def Pos.revSkip? {s : Slice} (pos : s.Pos) (pat : ρ) [BackwardPattern pat] : Option s.Pos :=
  ((s.sliceTo pos).skipSuffix? pat).map Pos.ofSliceTo

/--
If {name}`pat` matches a suffix of {name}`s`, returns the remainder. Returns {name}`none` otherwise.

Use {name (scope := "Init.Data.String.Slice.Pattern")}`String.Slice.dropSuffix` to return the slice
unchanged when {name}`pat` does not match a suffix.

This function is generic over all currently supported patterns.

Examples:
 * {lean}`"red green blue".toSlice.dropSuffix? " blue" == some "red green".toSlice`
 * {lean}`"red green blue".toSlice.dropSuffix? "bluu " == none`
 * {lean}`"red green blue".toSlice.dropSuffix? 'e' == some "red green blu".toSlice`
 * {lean}`"red green blue".toSlice.dropSuffix? Char.isLower == some "red green blu".toSlice`
-/
@[inline]
def dropSuffix? (s : Slice) (pat : ρ) [BackwardPattern pat] : Option Slice :=
  (s.skipSuffix? pat).map s.sliceTo

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
Rewinds {name}`pos` as long as {name}`pat` matches.
-/
@[specialize pat]
def Pos.revSkipWhile {s : Slice} (pos : s.Pos) (pat : ρ) [BackwardPattern pat] : s.Pos :=
  match pos.revSkip? pat with
  | some nextCurr =>
    if nextCurr < pos then
      revSkipWhile nextCurr pat
    else
      pos
  | none => pos
termination_by pos.down

/--
Returns the position at the start of the longest suffix of {name}`s` for which {name}`pat` matches
(potentially repeatedly).
-/
@[inline]
def skipSuffixWhile (s : Slice) (pat : ρ) [BackwardPattern pat] : s.Pos :=
  s.endPos.revSkipWhile pat

/--
Checks whether a slice only consists of matches of the pattern {name}`pat`, starting from the back
of the string.

Short-circuits at the first pattern mis-match.

This function is generic over all currently supported patterns.

For many types of patterns, this function can be expected to return the same result as
{name}`Slice.all`. If mismatches are expected to occur close to the end of the string, this function
might be more efficient.

For some types of patterns, this function will return a different result than {name}`Slice.all`.
Consider, for example, a pattern that matches the longest string at the given position that matches
the regular expression {lean}`"a|aa|ab"`. Then, given the input string {lean}`"aab"`, performing
{name}`Slice.all` will greedily match the prefix {lean}`"aa"` and then get stuck on the remainder
{lean}`"b"`, causing it to return {lean}`false`. On the other hand, {name}`Slice.revAll` will match
the suffix {lean}`"ab"` and then match the remainder {lean}`"a"`, so it will return {lean}`true`.

Examples:
 * {lean}`"brown".toSlice.revAll Char.isLower = true`
 * {lean}`"brown and orange".toSlice.revAll Char.isLower = false`
 * {lean}`"aaaaaa".toSlice.revAll 'a' = true`
 * {lean}`"aaaaaa".toSlice.revAll "aa" = true`
 * {lean}`"aaaaaaa".toSlice.revAll "aa" = false`
-/
@[inline]
def revAll (s : Slice) (pat : ρ) [BackwardPattern pat] : Bool :=
  s.skipSuffixWhile pat == s.startPos

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
  s.sliceTo (s.skipSuffixWhile pat)

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
  s.sliceFrom (s.skipSuffixWhile pat)

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

end String.Slice
