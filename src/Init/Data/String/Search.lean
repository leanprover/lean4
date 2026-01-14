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
variable [∀ s, Std.Iterator (σ s) Id (SearchStep s)]
variable [∀ s, Std.Iterators.Finite (σ s) Id]
variable [∀ s, Std.IteratorLoop (σ s) Id Id]


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
{name}`pos`. If there is no match {lean}`s.endPos` is returned.

This function is generic over all currently supported patterns.

Examples:
 * {lean}`("coffee tea water".toSlice.startPos.find Char.isWhitespace).get! == ' '`
 * {lean}`("tea".toSlice.pos ⟨1⟩ (by decide)).find (fun (c : Char) => c == 't') == "tea".toSlice.endPos`
-/
@[inline]
def Slice.Pos.find {s : Slice} (pos : s.Pos) (pattern : ρ) [ToForwardSearcher pattern σ] :
    s.Pos :=
  ofSliceFrom ((s.sliceFrom pos).find pattern)

/--
Finds the position of the first match of the pattern {name}`pattern` in after the position
{name}`pos`. If there is no match {name}`none` is returned.

This function is generic over all currently supported patterns.

Examples:
 * {lean}`("coffee tea water".startPos.find? Char.isWhitespace).map (·.get!) == some ' '`
 * {lean}`("tea".pos ⟨1⟩ (by decide)).find? (fun (c : Char) => c == 't') == none`
-/
@[inline]
def Pos.find?  {s : String} (pos : s.Pos) (pattern : ρ)
    [ToForwardSearcher pattern σ] : Option s.Pos :=
  (pos.toSlice.find? pattern).map Pos.ofToSlice

/--
Finds the position of the first match of the pattern {name}`pattern` in after the position
{name}`pos`. If there is no match {lean}`s.endPos` is returned.

This function is generic over all currently supported patterns.

Examples:
 * {lean}`("coffee tea water".startPos.find Char.isWhitespace).get! == ' '`
 * {lean}`("tea".pos ⟨1⟩ (by decide)).find (fun (c : Char) => c == 't') == "tea".endPos`
-/
@[inline]
def Pos.find {s : String} (pos : s.Pos) (pattern : ρ) [ToForwardSearcher pattern σ] :
    s.Pos :=
  ofToSlice (pos.toSlice.find pattern)

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
def find? (s : String) (pattern : ρ) [ToForwardSearcher pattern σ] : Option s.Pos :=
  s.startPos.find? pattern

/--
Finds the position of the first match of the pattern {name}`pattern` in a slice {name}`s`. If there
is no match {lean}`s.endPos` is returned.

This function is generic over all currently supported patterns.

Examples:
 * {lean}`("coffee tea water".find Char.isWhitespace).get! == ' '`
 * {lean}`"tea".find (fun (c : Char) => c == 'X') == "tea".endPos`
 * {lean}`("coffee tea water".find "tea").get! == 't'`
-/
@[inline]
def find (s : String) (pattern : ρ) [ToForwardSearcher pattern σ] : s.Pos :=
  s.startPos.find pattern

/--
Finds the position of the first match of the pattern {name}`pattern` in a slice {name}`s` that is
strictly before {name}`pos`. If there is no such match {lean}`none` is returned.

This function is generic over all currently supported patterns except
{name}`String`/{name}`String.Slice`.

Examples:
* {lean}`(("abc".toSlice.endPos.prev (by decide)).revFind? Char.isAlpha).map (·.get!) == some 'b'`
* {lean}`"abc".toSlice.startPos.revFind? Char.isAlpha == none`

-/
@[inline]
def Slice.Pos.revFind? {s : Slice} (pos : s.Pos) (pattern : ρ) [ToBackwardSearcher pattern σ] :
    Option s.Pos :=
  ((s.sliceTo pos).revFind? pattern).map ofSliceTo

/--
Finds the position of the first match of the pattern {name}`pattern` in a slice {name}`s` that is
strictly before {name}`pos`. If there is no such match {lean}`none` is returned.

This function is generic over all currently supported patterns except
{name}`String`/{name}`String.Slice`.

Examples:
* {lean}`(("ab1c".endPos.prev (by decide)).revFind? Char.isAlpha).map (·.get!) == some 'b'`
* {lean}`"abc".startPos.revFind? Char.isAlpha == none`
-/
@[inline]
def Pos.revFind? {s : String} (pos : s.Pos) (pattern : ρ) [ToBackwardSearcher pattern σ] :
    Option s.Pos :=
  (pos.toSlice.revFind? pattern).map Pos.ofToSlice

/--
Finds the position of the first match of the pattern {name}`pattern` in a string, starting
from the end of the slice and traversing towards the start. If there is no match {name}`none` is
returned.

This function is generic over all currently supported patterns except
{name}`String`/{name}`String.Slice`.

Examples:
 * {lean}`("coffee tea water".toSlice.revFind? Char.isWhitespace).map (·.get!) == some ' '`
 * {lean}`"tea".toSlice.revFind? (fun (c : Char) => c == 'X') == none`
-/
@[inline]
def revFind? (s : String) (pattern : ρ) [ToBackwardSearcher pattern σ] : Option s.Pos :=
  s.endPos.revFind? pattern

@[export lean_string_posof]
def Internal.posOfImpl (s : String) (c : Char) : Pos.Raw :=
  (s.find c).offset

@[deprecated String.Pos.find (since := "2025-11-19")]
def findAux (s : String) (p : Char → Bool) (stopPos : Pos.Raw) (pos : Pos.Raw) : Pos.Raw :=
  if h : pos ≤ stopPos ∧ pos.IsValid s ∧ stopPos.IsValid s then
    (String.Slice.mk s (s.pos pos h.2.1) (s.pos stopPos h.2.2)
      (by simp [Pos.le_iff, h.1])).find p |>.str.offset
  else stopPos

@[deprecated String.Pos.find (since := "2025-11-19")]
def posOfAux (s : String) (c : Char) (stopPos : Pos.Raw) (pos : Pos.Raw) : Pos.Raw :=
  if h : pos ≤ stopPos ∧ pos.IsValid s ∧ stopPos.IsValid s then
    (String.Slice.mk s (s.pos pos h.2.1) (s.pos stopPos h.2.2)
      (by simp [Pos.le_iff, h.1])).find c |>.str.offset
  else stopPos

@[deprecated String.find (since := "2025-11-19")]
def posOf (s : String) (c : Char) : Pos.Raw :=
  (s.find c).offset

@[deprecated String.Pos.revFind? (since := "2025-11-19")]
def revPosOfAux (s : String) (c : Char) (pos : Pos.Raw) : Option Pos.Raw :=
  s.pos? pos |>.bind (·.revFind? c) |>.map (·.offset)

@[deprecated String.revFind? (since := "2025-11-19")]
def revPosOf (s : String) (c : Char) : Option Pos.Raw :=
  s.revFind? c |>.map (·.offset)

@[deprecated String.Pos.revFind? (since := "2025-11-19")]
def revFindAux (s : String) (p : Char → Bool) (pos : Pos.Raw) : Option Pos.Raw :=
  s.pos? pos |>.bind (·.revFind? p) |>.map (·.offset)

@[deprecated String.revFind? (since := "2025-11-19")]
def revFind (s : String) (p : Char → Bool) : Option Pos.Raw :=
  s.revFind? p |>.map (·.offset)

/--
Returns the position of the beginning of the line that contains the position {name}`pos`.

Lines are ended by {lean}`'\n'`, and the returned position is either {lean}`0 : String.Pos.Raw` or
immediately after a {lean}`'\n'` character.
-/
@[deprecated String.Pos.revFind? (since := "2025-11-19")]
def findLineStart (s : String) (pos : String.Pos.Raw) : String.Pos.Raw :=
  s.pos? pos |>.bind (·.revFind? '\n') |>.map (·.offset) |>.getD s.startPos.offset

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
def split (s : String) (pat : ρ) [ToForwardSearcher pat σ] :=
  (s.toSlice.split pat : Std.Iter String.Slice)

/--
Splits a string at each subslice that matches the pattern {name}`pat`. Unlike {name}`split` the
matched subslices are included at the end of each subslice.

This function is generic over all currently supported patterns.

Examples:
 * {lean}`("coffee tea water".splitInclusive Char.isWhitespace).toList == ["coffee ".toSlice, "tea ".toSlice, "water".toSlice]`
 * {lean}`("coffee tea water".splitInclusive ' ').toList == ["coffee ".toSlice, "tea ".toSlice, "water".toSlice]`
 * {lean}`("coffee tea water".splitInclusive " tea ").toList == ["coffee tea ".toSlice, "water".toSlice]`
 * {lean}`("baaab".splitInclusive "aa").toList == ["baa".toSlice, "ab".toSlice]`
-/
@[inline]
def splitInclusive (s : String) (pat : ρ) [ToForwardSearcher pat σ] :=
  (s.toSlice.splitInclusive pat : Std.Iter String.Slice)

@[deprecated String.Slice.foldl (since := "2025-11-20")]
def foldlAux {α : Type u} (f : α → Char → α) (s : String) (stopPos : Pos.Raw) (i : Pos.Raw) (a : α) : α :=
  s.slice! (s.pos! i) (s.pos! stopPos) |>.foldl f a

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

@[deprecated String.Slice.foldr (since := "2025-11-25")]
def foldrAux {α : Type u} (f : Char → α → α) (a : α) (s : String) (i begPos : Pos.Raw) : α :=
  s.slice! (s.pos! begPos) (s.pos! i) |>.foldr f a

/--
Folds a function over a string from the right, accumulating a value starting with {lean}`init`. The
accumulated value is combined with each character in reverse order, using {lean}`f`.

Examples:
 * {lean}`"coffee tea water".foldr (fun c n => if c.isWhitespace then n + 1 else n) 0 = 2`
 * {lean}`"coffee tea and water".foldr (fun c n => if c.isWhitespace then n + 1 else n) 0 = 3`
 * {lean}`"coffee tea water".foldr (fun c s => s.push c) "" = "retaw aet eeffoc"`
-/
@[inline] def foldr {α : Type u} (f : Char → α → α) (init : α) (s : String) : α :=
  s.toSlice.foldr f init

@[deprecated String.Slice.any (since := "2025-11-25")]
def anyAux (s : String) (stopPos : Pos.Raw) (p : Char → Bool) (i : Pos.Raw) : Bool :=
  s.slice! (s.pos! i) (s.pos! stopPos) |>.any p


/--
Checks whether a string has a match of the pattern {name}`pat` anywhere.

This function is generic over all currently supported patterns.

Examples:
 * {lean}`"coffee tea water".contains Char.isWhitespace = true`
 * {lean}`"tea".contains (fun (c : Char) => c == 'X') = false`
 * {lean}`"coffee tea water".contains "tea" = true`
-/
@[inline, suggest_for String.some]
def contains (s : String) (pat : ρ) [ToForwardSearcher pat σ] : Bool :=
  s.toSlice.contains pat

@[export lean_string_contains]
def Internal.containsImpl (s : String) (c : Char) : Bool :=
  String.contains s c

@[inline, inherit_doc contains] def any (s : String) (pat : ρ) [ToForwardSearcher pat σ] : Bool :=
  s.contains pat

@[export lean_string_any]
def Internal.anyImpl (s : String) (p : Char → Bool) :=
  String.any s p

/--
Checks whether a slice only consists of matches of the pattern {name}`pat`.

Short-circuits at the first pattern mis-match.

This function is generic over all currently supported patterns.

Examples:
 * {lean}`"brown".all Char.isLower = true`
 * {lean}`"brown and orange".all Char.isLower = false`
 * {lean}`"aaaaaa".all 'a' = true`
 * {lean}`"aaaaaa".all "aa" = true`
 * {lean}`"aaaaaaa".all "aa" = false`
-/
@[inline, suggest_for String.every] def all (s : String) (pat : ρ) [ForwardPattern pat] : Bool :=
  s.toSlice.all pat

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

/--
Interprets a string as the decimal representation of an integer, returning it. Returns {lean}`none`
if the string does not contain a decimal integer.

A string can be interpreted as a decimal integer if it only consists of at least one decimal digit
and optionally {lit}`-` in front. Leading `+` characters are not allowed.

Use {name (scope := "Init.Data.String.Search")}`String.isInt` to check whether {name}`String.toInt?`
would return {lean}`some`. {name (scope := "Init.Data.String.Search")}`String.toInt!` is an
alternative that panics instead of returning {lean}`none` when the string is not an integer.

Examples:
 * {lean}`"".toInt? = none`
 * {lean}`"-".toInt? = none`
 * {lean}`"0".toInt? = some 0`
 * {lean}`"5".toInt? = some 5`
 * {lean}`"-5".toInt? = some (-5)`
 * {lean}`"587".toInt? = some 587`
 * {lean}`"-587".toInt? = some (-587)`
 * {lean}`" 5".toInt? = none`
 * {lean}`"2-3".toInt? = none`
 * {lean}`"0xff".toInt? = none`
-/
@[inline] def toInt? (s : String) : Option Int :=
  s.toSlice.toInt?

/--
Checks whether the string can be interpreted as the decimal representation of an integer.

A string can be interpreted as a decimal integer if it only consists of at least one decimal digit
and optionally {lit}`-` in front. Leading `+` characters are not allowed.

Use {name}`String.toInt?` or {name (scope := "Init.Data.String.Search")}`String.toInt!` to convert
such a string to an integer.

Examples:
 * {lean}`"".isInt = false`
 * {lean}`"-".isInt = false`
 * {lean}`"0".isInt = true`
 * {lean}`"-0".isInt = true`
 * {lean}`"5".isInt = true`
 * {lean}`"587".isInt = true`
 * {lean}`"-587".isInt = true`
 * {lean}`"+587".isInt = false`
 * {lean}`" 5".isInt = false`
 * {lean}`"2-3".isInt = false`
 * {lean}`"0xff".isInt = false`
-/
@[inline] def isInt (s : String) : Bool :=
  s.toSlice.isInt

/--
Interprets a string as the decimal representation of an integer, returning it. Panics if the string
does not contain a decimal integer.

A string can be interpreted as a decimal integer if it only consists of at least one decimal digit
and optionally {lit}`-` in front. Leading `+` characters are not allowed.

Use {name}`String.isInt` to check whether {name}`String.toInt!` would return a value.
{name}`String.toInt?` is a safer alternative that returns {lean}`none` instead of panicking when the
string is not an integer.

Examples:
 * {lean}`"0".toInt! = 0`
 * {lean}`"5".toInt! = 5`
 * {lean}`"587".toInt! = 587`
 * {lean}`"-587".toInt! = -587`
-/
@[inline] def toInt! (s : String) : Int :=
  s.toSlice.toInt!


/--
Returns the first character in {name}`s`. If {name}`s` is empty, returns {name}`none`.

Examples:
* {lean}`"abc".front? = some 'a'`
* {lean}`"".front? = none`
-/
@[inline]
def front? (s : String) : Option Char :=
  s.toSlice.front?

/--
Returns the first character in {name}`s`. If {lean}`s = ""`, returns {lean}`(default : Char)`.

Examples:
* {lean}`"abc".front = 'a'`
* {lean}`"".front = (default : Char)`
-/
@[inline, expose] def front (s : String) : Char :=
  s.toSlice.front

@[export lean_string_front]
def Internal.frontImpl (s : String) : Char :=
  String.front s

/--
Returns the last character in {name}`s`. If {name}`s` is empty, returns {name}`none`.

Examples:
* {lean}`"abc".back? = some 'c'`
* {lean}`"".back? = none`
-/
@[inline]
def back? (s : String) : Option Char :=
  s.toSlice.back?


/--
Returns the last character in {name}`s`. If {lean}`s = ""`, returns {lean}`(default : Char)`.

Examples:
* {lean}`"abc".back = 'c'`
* {lean}`"".back = (default : Char)`
-/
@[inline, expose] def back (s : String) : Char :=
  s.toSlice.back

theorem Pos.ofToSlice_ne_endPos {s : String} {p : s.toSlice.Pos}
    (h : p ≠ s.toSlice.endPos) : ofToSlice p ≠ s.endPos := by
  rwa [ne_eq, ← Pos.toSlice_inj, Slice.Pos.toSlice_ofToSlice, ← endPos_toSlice]

@[inline]
def Internal.toSliceWithProof {s : String} :
    { p : s.toSlice.Pos // p ≠ s.toSlice.endPos } → { p : s.Pos // p ≠ s.endPos } :=
  fun ⟨p, h⟩ => ⟨Pos.ofToSlice p, Pos.ofToSlice_ne_endPos h⟩

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

/--
Creates an iterator over all lines in {name}`s` with the line ending characters `\r\n` or `\n` being
stripped.

Examples:
 * {lean}`"foo\r\nbar\n\nbaz\n".lines.toList  == ["foo".toSlice, "bar".toSlice, "".toSlice, "baz".toSlice]`
 * {lean}`"foo\r\nbar\n\nbaz".lines.toList  == ["foo".toSlice, "bar".toSlice, "".toSlice, "baz".toSlice]`
 * {lean}`"foo\r\nbar\n\nbaz\r".lines.toList  == ["foo".toSlice, "bar".toSlice, "".toSlice, "baz\r".toSlice]`
-/
def lines (s : String) :=
  s.toSlice.lines

end

end String
