/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

prelude
public import Init.Data.String.Slice

set_option doc.verso true

/-!
# String operations based on slice operations

This file contains {name}`String` operations that are implemented by passing to
{name}`String.Slice`.
-/

public section

namespace String

section
open String.Slice Pattern

variable {ρ : Type} {σ : Slice → Type}
variable [∀ s, Std.Iterators.Iterator (σ s) Id (SearchStep s)]
variable [∀ s, Std.Iterators.Finite (σ s) Id]
variable [∀ s, Std.Iterators.IteratorLoop (σ s) Id Id]


/--
Constructs a new string obtained by replacing all occurrences of {name}`pattern` with
{name}`replacement` in {name}`s`.

This function is generic over all currently supported patterns. The replacement may be a
{name}`String` or a {name}`String.Slice`.

Examples:
* {lean}`"red green blue".replace 'e' "" = "rd grn blu"`
* {lean}`"red green blue".replace (fun c => c == 'u' || c == 'e') "" = "rd grn bl"`
* {lean}`"red green blue".replace "e" "" = "rd grn blu"`
* {lean}`"red green blue".replace "ee" "E" = "red grEn blue"`
* {lean}`"red green blue".replace "e" "E" = "rEd grEEn bluE"`
* {lean}`"aaaaa".replace "aa" "b" = "bba"`
* {lean}`"abc".replace "" "k" = "kakbkck"`
-/
@[inline]
def replace [ToSlice α] (s : String) (pattern : ρ) [ToForwardSearcher pattern σ]
    (replacement : α) : String :=
  s.toSlice.replace pattern replacement

/--
Finds the position of the first match of the pattern {name}`pattern` in after the position
{name}`pos`. If there is no match {name}`none` is returned.

This function is generic over all currently supported patterns.

Examples:
 * {lean}`("coffee tea water".toSlice.startPos.find? Char.isWhitespace).map (·.get!) == some ' '`
 * {lean}`("tea".toSlice.pos ⟨1⟩ (by decide)).find? (fun (c : Char) => c == 't') == none`
-/
@[inline]
def Slice.Pos.find? {s : Slice} (pos : s.Pos) (pattern : ρ) [ToForwardSearcher pattern σ]  :
    Option s.Pos :=
  ((s.sliceFrom pos).find? pattern).map ofSliceFrom

/--
Finds the position of the first match of the pattern {name}`pattern` in after the position
{name}`pos`. If there is no match {name}`none` is returned.

This function is generic over all currently supported patterns.

Examples:
 * {lean}`("coffee tea water".startValidPos.find? Char.isWhitespace).map (·.get!) == some ' '`
 * {lean}`("tea".pos ⟨1⟩ (by decide)).find? (fun (c : Char) => c == 't') == none`
-/
@[inline]
def ValidPos.find?  {s : String} (pos : s.ValidPos) (pattern : ρ)
    [ToForwardSearcher pattern σ] : Option s.ValidPos :=
  (pos.toSlice.find? pattern).map (·.ofSlice)

/--
Finds the position of the first match of the pattern {name}`pattern` in a string {name}`s`. If
there is no match {name}`none` is returned.

This function is generic over all currently supported patterns.

Examples:
 * {lean}`("coffee tea water".find? Char.isWhitespace).map (·.get!) == some ' '`
 * {lean}`"tea".find? (fun (c : Char) => c == 'X') == none`
 * {lean}`("coffee tea water".find? "tea").map (·.get!) == some 't'`
-/
@[inline]
def find? (s : String) (pattern : ρ) [ToForwardSearcher pattern σ] : Option s.ValidPos :=
  s.startValidPos.find? pattern

/--
Splits a string at each subslice that matches the pattern {name}`pat`.

The subslices that matched the pattern are not included in any of the resulting subslices. If
multiple subslices in a row match the pattern, the resulting list will contain empty strings.

This function is generic over all currently supported patterns.

Examples:
 * {lean}`("coffee tea water".split Char.isWhitespace).toList == ["coffee".toSlice, "tea".toSlice, "water".toSlice]`
 * {lean}`("coffee tea water".split ' ').toList == ["coffee".toSlice, "tea".toSlice, "water".toSlice]`
 * {lean}`("coffee tea water".split " tea ").toList == ["coffee".toSlice, "water".toSlice]`
 * {lean}`("ababababa".split "aba").toList == ["coffee".toSlice, "water".toSlice]`
 * {lean}`("baaab".split "aa").toList == ["b".toSlice, "ab".toSlice]`
-/
@[inline]
def split (s : String) (pat : ρ) [ToForwardSearcher pat σ]  :=
  (s.toSlice.split pat : Std.Iter String.Slice)

@[deprecated String.Slice.foldl (since := "2025-11-20")]
def foldlAux {α : Type u} (f : α → Char → α) (s : String) (stopPos : Pos.Raw) (i : Pos.Raw) (a : α) : α :=
  s.replaceStartEnd! (s.pos! i) (s.pos! stopPos) |>.foldl f a

/--
Folds a function over a string from the start, accumulating a value starting with {name}`init`. The
accumulated value is combined with each character in order, using {name}`f`.

Examples:
 * {lean}`"coffee tea water".foldl (fun n c => if c.isWhitespace then n + 1 else n) 0 = 2`
 * {lean}`"coffee tea and water".foldl (fun n c => if c.isWhitespace then n + 1 else n) 0 = 3`
 * {lean}`"coffee tea water".foldl (·.push ·) "" = "coffee tea water"`
-/
@[inline] def foldl {α : Type u} (f : α → Char → α) (init : α) (s : String) : α :=
  s.toSlice.foldl f init

@[export lean_string_foldl]
def Internal.foldlImpl (f : String → Char → String) (init : String) (s : String) : String :=
  String.foldl f init s

/--
Checks whether the string can be interpreted as the decimal representation of a natural number.

A slice can be interpreted as a decimal natural number if it is not empty and all the characters in
it are digits.

Use {name (scope := "Init.Data.String.Search")}`toNat?` or
{name (scope := "Init.Data.String.Search")}`toNat!` to convert such a slice to a natural number.

Examples:
 * {lean}`"".isNat = false`
 * {lean}`"0".isNat = true`
 * {lean}`"5".isNat = true`
 * {lean}`"05".isNat = true`
 * {lean}`"587".isNat = true`
 * {lean}`"-587".isNat = false`
 * {lean}`" 5".isNat = false`
 * {lean}`"2+3".isNat = false`
 * {lean}`"0xff".isNat = false`
-/
@[inline] def isNat (s : String) : Bool :=
  s.toSlice.isNat

/--
Interprets a string as the decimal representation of a natural number, returning it. Returns
{name}`none` if the slice does not contain a decimal natural number.

A slice can be interpreted as a decimal natural number if it is not empty and all the characters in
it are digits.

Use {name}`isNat` to check whether {name}`toNat?` would return {name}`some`.
{name (scope := "Init.Data.String.Search")}`toNat!` is an alternative that panics instead of
returning {name}`none` when the slice is not a natural number.

Examples:
 * {lean}`"".toNat? = none`
 * {lean}`"0".toNat? = some 0`
 * {lean}`"5".toNat? = some 5`
 * {lean}`"587".toNat? = some 587`
 * {lean}`"-587".toNat? = none`
 * {lean}`" 5".toNat? = none`
 * {lean}`"2+3".toNat? = none`
 * {lean}`"0xff".toNat? = none`
-/
@[inline] def toNat? (s : String) : Option Nat :=
  s.toSlice.toNat?

/--
Interprets a string as the decimal representation of a natural number, returning it. Panics if the
slice does not contain a decimal natural number.

A slice can be interpreted as a decimal natural number if it is not empty and all the characters in
it are digits.

Use {name}`isNat` to check whether {name}`toNat!` would return a value. {name}`toNat?` is a safer
alternative that returns {name}`none` instead of panicking when the string is not a natural number.

Examples:
 * {lean}`"0".toNat! = 0`
 * {lean}`"5".toNat! = 5`
 * {lean}`"587".toNat! = 587`
-/
@[inline] def toNat! (s : String) : Nat :=
  s.toSlice.toNat!

end

end String
