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
def replace [ToForwardSearcher ρ σ] [ToSlice α] (s : String) (pattern : ρ)
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
def Slice.Pos.find? [ToForwardSearcher ρ σ] {s : Slice} (pos : s.Pos) (pattern : ρ) :
    Option s.Pos :=
  ((s.replaceStart pos).find? pattern).map ofReplaceStart

/--
Finds the position of the first match of the pattern {name}`pattern` in after the position
{name}`pos`. If there is no match {name}`none` is returned.

This function is generic over all currently supported patterns.

Examples:
 * {lean}`("coffee tea water".startValidPos.find? Char.isWhitespace).map (·.get!) == some ' '`
 * {lean}`("tea".pos ⟨1⟩ (by decide)).find? (fun (c : Char) => c == 't') == none`
-/
@[inline]
def ValidPos.find? [ToForwardSearcher ρ σ] {s : String} (pos : s.ValidPos)
    (pattern : ρ) : Option s.ValidPos :=
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
def find? [ToForwardSearcher ρ σ] (s : String) (pattern : ρ) : Option s.ValidPos :=
  s.startValidPos.find? pattern

end

end String
