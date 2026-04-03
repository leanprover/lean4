/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Mario Carneiro, Markus Himmel
-/
module

prelude
public import Init.Data.String.Substring

set_option doc.verso true

/-!
# `String.take` and variants

This file contains the implementations of `String.take` and its variants.
-/

public section

namespace String

variable {ρ : Type}

open Slice.Pattern

/--
Returns a {name}`String.Slice` obtained by removing the specified number of characters (Unicode code
points) from the start of the string.

If {name}`n` is greater than {lean}`s.length`, returns an empty slice.

This is a cheap operation because it does not allocate a new string to hold the result.
To convert the result into a string, use {name}`String.Slice.copy`.

Examples:
 * {lean}`"red green blue".drop 4 == "green blue".toSlice`
 * {lean}`"red green blue".drop 10 == "blue".toSlice`
 * {lean}`"red green blue".drop 50 == "".toSlice`
 * {lean}`"مرحبا بالعالم".drop 3 == "با بالعالم".toSlice`
-/
@[inline] def drop (s : String) (n : Nat) : Slice :=
  s.toSlice.drop n

@[export lean_string_drop]
def Internal.dropImpl (s : String) (n : Nat) : String :=
  (String.drop s n).copy

/--
Returns a {name}`String.Slice` obtained by removing the specified number of characters (Unicode code
points) from the end of the string.

If {name}`n` is greater than {lean}`s.length`, returns an empty slice.

This is a cheap operation because it does not allocate a new string to hold the result.
To convert the result into a string, use {name}`String.Slice.copy`.

Examples:
 * {lean}`"red green blue".dropEnd 5 == "red green".toSlice`
 * {lean}`"red green blue".dropEnd 11 == "red".toSlice`
 * {lean}`"red green blue".dropEnd 50 == "".toSlice`
 * {lean}`"مرحبا بالعالم".dropEnd 3 == "مرحبا بالع".toSlice`
-/
@[inline] def dropEnd (s : String) (n : Nat) : Slice :=
  s.toSlice.dropEnd n

@[deprecated String.dropEnd (since := "2025-11-14")]
def dropRight (s : String) (n : Nat) : String :=
  (s.dropEnd n).copy

@[deprecated Slice.dropEnd (since := "2025-11-20")]
def Slice.dropRight (s : Slice) (n : Nat) : Slice :=
  s.dropEnd n

@[export lean_string_dropright]
def Internal.dropRightImpl (s : String) (n : Nat) : String :=
  (String.dropEnd s n).copy

/--
Returns a {name}`String.Slice` that contains the first {name}`n` characters (Unicode code points) of
{name}`s`.

If {name}`n` is greater than {lean}`s.length`, returns {lean}`s.toSlice`.

This is a cheap operation because it does not allocate a new string to hold the result.
To convert the result into a string, use {name}`String.Slice.copy`.

Examples:
* {lean}`"red green blue".take 3 == "red".toSlice`
* {lean}`"red green blue".take 1 == "r".toSlice`
* {lean}`"red green blue".take 0 == "".toSlice`
* {lean}`"red green blue".take 100 == "red green blue".toSlice`
* {lean}`"مرحبا بالعالم".take 5 == "مرحبا".toSlice`
-/
@[inline] def take (s : String) (n : Nat) : String.Slice :=
  s.toSlice.take n

/--
Returns a {name}`String.Slice` that contains the last {name}`n` characters (Unicode code points) of
{name}`s`.

If {name}`n` is greater than {lean}`s.length`, returns {lean}`s.toSlice`.

This is a cheap operation because it does not allocate a new string to hold the result.
To convert the result into a string, use {name}`String.Slice.copy`.

Examples:
* {lean}`"red green blue".takeEnd 4 == "blue".toSlice`
* {lean}`"red green blue".takeEnd 1 == "e".toSlice`
* {lean}`"red green blue".takeEnd 0 == "".toSlice`
* {lean}`"red green blue".takeEnd 100 == "red green blue".toSlice`
* {lean}`"مرحبا بالعالم".takeEnd 5 == "لعالم".toSlice`
-/
@[inline] def takeEnd (s : String) (n : Nat) : String.Slice :=
  s.toSlice.takeEnd n

@[deprecated String.takeEnd (since := "2025-11-14")]
def takeRight (s : String) (n : Nat) : String :=
  (s.takeEnd n).toString

@[deprecated Slice.takeEnd (since := "2025-11-20")]
def Slice.takeRight (s : Slice) (n : Nat) : Slice :=
  s.takeEnd n

/--
Creates a string slice that contains the longest prefix of {name}`s` in which {name}`pat` matched
(potentially repeatedly).

This is a cheap operation because it does not allocate a new string to hold the result.
To convert the result into a string, use {name}`String.Slice.copy`.

This function is generic over all currently supported patterns.

Examples:
 * {lean}`"red green blue".takeWhile Char.isLower == "red".toSlice`
 * {lean}`"red green blue".takeWhile 'r' == "r".toSlice`
 * {lean}`"red red green blue".takeWhile "red " == "red red ".toSlice`
 * {lean}`"red green blue".takeWhile (fun (_ : Char) => true) == "red green blue".toSlice`
-/
@[inline] def takeWhile (s : String) (pat : ρ) [ForwardPattern pat] : String.Slice :=
  s.toSlice.takeWhile pat

/--
Creates a string slice by removing the longest prefix from {name}`s` in which {name}`pat` matched
(potentially repeatedly).

This is a cheap operation because it does not allocate a new string to hold the result.
To convert the result into a string, use {name}`String.Slice.copy`.

This function is generic over all currently supported patterns.

Examples:
 * {lean}`"red green blue".dropWhile Char.isLower == " green blue".toSlice`
 * {lean}`"red green blue".dropWhile 'r' == "ed green blue".toSlice`
 * {lean}`"red red green blue".dropWhile "red " == "green blue".toSlice`
 * {lean}`"red green blue".dropWhile (fun (_ : Char) => true) == "".toSlice`
-/
@[inline] def dropWhile (s : String) (pat : ρ) [ForwardPattern pat] : String.Slice :=
  s.toSlice.dropWhile pat

/--
Creates a string slice that contains the longest suffix of {name}`s` in which {name}`pat` matched
(potentially repeatedly).

This is a cheap operation because it does not allocate a new string to hold the result.
To convert the result into a string, use {name}`String.Slice.copy`.

This function is generic over all currently supported patterns.

Examples:
 * {lean}`"red green blue".takeEndWhile Char.isLower == "blue".toSlice`
 * {lean}`"red green blue".takeEndWhile 'e' == "e".toSlice`
 * {lean}`"red green blue".takeEndWhile (fun (_ : Char) => true) == "red green blue".toSlice`
-/
@[inline] def takeEndWhile (s : String) (pat : ρ) [BackwardPattern pat] : String.Slice :=
  s.toSlice.takeEndWhile pat

@[deprecated String.takeEndWhile (since := "2025-11-17")]
def takeRightWhile (s : String) (p : Char → Bool) : String :=
  (s.takeEndWhile p).toString

@[deprecated Slice.takeEndWhile (since := "2025-11-20")]
def Slice.takeRightWhile (s : Slice) (p : Char → Bool) : Slice :=
  s.takeEndWhile p

/--
Creates a new string by removing the longest suffix from {name}`s` in which {name}`pat` matches
(potentially repeatedly).

This is a cheap operation because it does not allocate a new string to hold the result.
To convert the result into a string, use {name}`String.Slice.copy`.

This function is generic over all currently supported patterns.

Examples:
 * {lean}`"red green blue".dropEndWhile Char.isLower == "red green ".toSlice`
 * {lean}`"red green blue".dropEndWhile 'e' == "red green blu".toSlice`
 * {lean}`"red green blue".dropEndWhile (fun (_ : Char) => true) == "".toSlice`
-/
@[inline] def dropEndWhile (s : String) (pat : ρ) [BackwardPattern pat] : String.Slice :=
  s.toSlice.dropEndWhile pat

@[deprecated String.dropEndWhile (since := "2025-11-17")]
def dropRightWhile (s : String) (p : Char → Bool) : String :=
  (s.dropEndWhile p).toString

@[deprecated Slice.dropEndWhile (since := "2025-11-20")]
def Slice.dropRightWhile (s : Slice) (p : Char → Bool) : Slice :=
  s.dropEndWhile p

/--
If {name}`pat` matches a prefix of {name}`s`, returns the position at the start of the remainder.
Returns {name}`none` otherwise.

This function is generic over all currently supported patterns.
-/
@[inline] def skipPrefix? (s : String) (pat : ρ) [ForwardPattern pat] : Option s.Pos :=
  (s.toSlice.skipPrefix? pat).map Pos.ofToSlice

/--
Returns the position after the longest prefix of {name}`s` for which {name}`pat` matches
(potentially repeatedly).
-/
@[inline] def skipPrefixWhile (s : String) (pat : ρ) [ForwardPattern pat] : s.Pos :=
  Pos.ofToSlice (s.toSlice.skipPrefixWhile pat)

/--
Checks whether a string only consists of matches of the pattern {name}`pat`.

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
Checks whether a string only consists of matches of the pattern {name}`pat`, starting from the back
of the string.

Short-circuits at the first pattern mis-match.

This function is generic over all currently supported patterns.

For many types of patterns, this function can be expected to return the same result as
{name}`String.all`. If mismatches are expected to occur close to the end of the string, this function
might be more efficient.

For some types of patterns, this function will return a different result than {name}`String.all`.
Consider, for example, a pattern that matches the longest string at the given position that matches
the regular expression {lean}`"a|aa|ab"`. Then, given the input string {lean}`"aab"`, performing
{name}`String.all` will greedily match the prefix {lean}`"aa"` and then get stuck on the remainder
{lean}`"b"`, causing it to return {lean}`false`. On the other hand, {name}`String.revAll` will match
the suffix {lean}`"ab"` and then match the remainder {lean}`"a"`, so it will return {lean}`true`.

Examples:
 * {lean}`"brown".revAll Char.isLower = true`
 * {lean}`"brown and orange".revAll Char.isLower = false`
 * {lean}`"aaaaaa".revAll 'a' = true`
 * {lean}`"aaaaaa".revAll "aa" = true`
 * {lean}`"aaaaaaa".revAll "aa" = false`
-/
@[inline]
def revAll (s : String) (pat : ρ) [BackwardPattern pat] : Bool :=
  s.toSlice.revAll pat

/--
If {name}`pat` matches at {name}`pos`, returns the position after the end of the match.
Returns {name}`none` otherwise.

This function is generic over all currently supported patterns.
-/
@[inline]
def Pos.skip? {s : String} (pos : s.Pos) (pat : ρ) [ForwardPattern pat] : Option s.Pos :=
  (pos.toSlice.skip? pat).map Pos.ofToSlice

/--
Advances {name}`pos` as long as {name}`pat` matches.
-/
@[inline]
def Pos.skipWhile {s : String} (pos : s.Pos) (pat : ρ) [ForwardPattern pat] : s.Pos :=
  Pos.ofToSlice (pos.toSlice.skipWhile pat)

/--
Checks whether the first string ({name}`s`) begins with the pattern ({name}`pat`).

{name (scope := "Init.Data.String.TakeDrop")}`String.isPrefixOf` is a version that takes the
potential prefix before the string.

Examples:
 * {lean}`"red green blue".startsWith "red" = true`
 * {lean}`"red green blue".startsWith "green" = false`
 * {lean}`"red green blue".startsWith "" = true`
 * {lean}`"red green blue".startsWith 'r' = true`
 * {lean}`"red green blue".startsWith Char.isLower = true`
-/
@[inline] def startsWith (s : String) (pat : ρ) [ForwardPattern pat] : Bool :=
  s.toSlice.startsWith pat

/--
Checks whether the second string ({name}`s`) begins with a prefix ({name}`p`).

This function is generic over all currently supported patterns.

{name}`String.startsWith` is a version that takes the potential prefix after the string.

Examples:
 * {lean}`"red".isPrefixOf "red green blue" = true`
 * {lean}`"green".isPrefixOf "red green blue" = false`
 * {lean}`"".isPrefixOf "red green blue" = true`
-/
@[inline] def isPrefixOf (p : String) (s : String) : Bool :=
  s.startsWith p

@[export lean_string_isprefixof]
def Internal.isPrefixOfImpl (p : String) (s : String) : Bool :=
  String.isPrefixOf p s

/--
Checks whether the string ({name}`s`) ends with the pattern ({name}`pat`).

This function is generic over all currently supported patterns.

Examples:
 * {lean}`"red green blue".endsWith "blue" = true`
 * {lean}`"red green blue".endsWith "green" = false`
 * {lean}`"red green blue".endsWith "" = true`
 * {lean}`"red green blue".endsWith 'e' = true`
 * {lean}`"red green blue".endsWith Char.isLower = true`
-/
@[inline] def endsWith (s : String) (pat : ρ) [BackwardPattern pat] : Bool :=
  s.toSlice.endsWith pat

/--
If {name}`pat` matches a suffix of {name}`s`, returns the position at the beginning of the suffix.
Returns {name}`none` otherwise.

This function is generic over all currently supported patterns.
-/
@[inline] def skipSuffix? (s : String) (pat : ρ) [BackwardPattern pat] : Option s.Pos :=
  (s.toSlice.skipSuffix? pat).map Pos.ofToSlice

/--
Returns the position at the start of the longest suffix of {name}`s` for which {name}`pat` matches
(potentially repeatedly).
-/
@[inline] def skipSuffixWhile (s : String) (pat : ρ) [BackwardPattern pat] : s.Pos :=
  Pos.ofToSlice (s.toSlice.skipSuffixWhile pat)

/--
If {name}`pat` matches at {name}`pos`, returns the position after the end of the match.
Returns {name}`none` otherwise.

This function is generic over all currently supported patterns.
-/
@[inline]
def Pos.revSkip? {s : String} (pos : s.Pos) (pat : ρ) [BackwardPattern pat] : Option s.Pos :=
  (pos.toSlice.revSkip? pat).map Pos.ofToSlice

/--
Rewinds {name}`pos` as long as {name}`pat` matches.
-/
@[inline]
def Pos.revSkipWhile {s : String} (pos : s.Pos) (pat : ρ) [BackwardPattern pat] : s.Pos :=
  Pos.ofToSlice (pos.toSlice.revSkipWhile pat)

/--
Removes trailing whitespace from a string by returning a slice whose end position is the last
non-whitespace character, or the start position if there is no non-whitespace character.

“Whitespace” is defined as characters for which {name}`Char.isWhitespace` returns {name}`true`.

Examples:
 * {lean}`"abc".trimAsciiEnd == "abc".toSlice`
 * {lean}`"   abc".trimAsciiEnd == "   abc".toSlice`
 * {lean}`"abc \t  ".trimAsciiEnd == "abc".toSlice`
 * {lean}`"  abc   ".trimAsciiEnd == "  abc".toSlice`
 * {lean}`"abc\ndef\n".trimAsciiEnd == "abc\ndef".toSlice`
-/
@[inline] def trimAsciiEnd (s : String) : String.Slice :=
  s.toSlice.trimAsciiEnd

@[deprecated String.trimAsciiEnd (since := "2025-11-17")]
def trimRight (s : String) : String :=
  s.trimAsciiEnd.copy

@[deprecated Slice.trimAsciiEnd (since := "2025-11-20")]
def Slice.trimRight (s : Slice) : Slice :=
  s.trimAsciiEnd

/--
Removes leading whitespace from a string by returning a slice whose start position is the first
non-whitespace character, or the end position if there is no non-whitespace character.

“Whitespace” is defined as characters for which {name}`Char.isWhitespace` returns {name}`true`.

Examples:
 * {lean}`"abc".trimAsciiStart == "abc".toSlice`
 * {lean}`"   abc".trimAsciiStart == "abc".toSlice`
 * {lean}`"abc \t  ".trimAsciiStart == "abc \t  ".toSlice`
 * {lean}`"  abc   ".trimAsciiStart == "abc   ".toSlice`
 * {lean}`"abc\ndef\n".trimAsciiStart == "abc\ndef\n".toSlice`
-/
@[inline] def trimAsciiStart (s : String) : String.Slice :=
  s.toSlice.trimAsciiStart

@[deprecated String.trimAsciiStart (since := "2025-11-17")]
def trimLeft (s : String) : String :=
  s.trimAsciiStart.copy

@[deprecated Slice.trimAsciiStart (since := "2025-11-20")]
def Slice.trimLeft (s : Slice) : Slice :=
  s.trimAsciiStart

/--
Removes leading and trailing whitespace from a string.

“Whitespace” is defined as characters for which {name}`Char.isWhitespace` returns {name}`true`.

Examples:
 * {lean}`"abc".trimAscii == "abc".toSlice`
 * {lean}`"   abc".trimAscii == "abc".toSlice`
 * {lean}`"abc \t  ".trimAscii == "abc".toSlice`
 * {lean}`"  abc   ".trimAscii == "abc".toSlice`
 * {lean}`"abc\ndef\n".trimAscii == "abc\ndef".toSlice`
-/
@[inline] def trimAscii (s : String) : String.Slice :=
  s.toSlice.trimAscii

@[deprecated String.trimAscii (since := "2025-11-17")]
def trim (s : String) : String :=
  s.trimAscii.copy

@[deprecated Slice.trimAscii (since := "2025-11-20")]
def Slice.trim (s : Slice) : Slice :=
  s.trimAscii

@[export lean_string_trim]
def Internal.trimImpl (s : String) : String :=
  (String.trimAscii s).copy

/--
Repeatedly increments a position in a string, as if by {name}`String.Pos.Raw.next`, while the
predicate {name}`p` returns {lean}`true` for the character at the position. Stops incrementing at
the end of the string or when {name}`p` returns {lean}`false` for the current character.

Examples:
* {lean}`let s := "   a  "; ((0 : Pos.Raw).nextWhile s Char.isWhitespace).get s = 'a'`
* {lean}`let s := "a  "; ((0 : Pos.Raw).nextWhile s Char.isWhitespace).get s = 'a'`
* {lean}`let s := "ba  "; (Pos.Raw.nextWhile s Char.isWhitespace 0).get s = 'b'`
-/
@[inline] def Pos.Raw.nextWhile (s : String) (p : Char → Bool) (i : String.Pos.Raw) : String.Pos.Raw :=
  Substring.Raw.takeWhileAux s s.rawEndPos p i

@[deprecated Pos.Raw.nextWhile (since := "2025-10-10")]
abbrev nextWhile (s : String) (p : Char → Bool) (i : String.Pos.Raw) : String.Pos.Raw :=
  Pos.Raw.nextWhile s p i

@[export lean_string_nextwhile]
def Internal.nextWhileImpl (s : String) (p : Char → Bool) (i : String.Pos.Raw) : String.Pos.Raw :=
  i.nextWhile s p

/--
Repeatedly increments a position in a string, as if by {name}`String.Pos.Raw.next`, while the predicate
{name}`p` returns {lean}`false` for the character at the position. Stops incrementing at the end of
the string or when {name}`p` returns {lean}`true` for the current character.

Examples:
* {lean}`let s := "   a  "; (Pos.Raw.nextUntil s Char.isWhitespace 0).get s = ' '`
* {lean}`let s := "   a  "; (Pos.Raw.nextUntil s Char.isAlpha 0).get s = 'a'`
* {lean}`let s := "a  "; (Pos.Raw.nextUntil s Char.isWhitespace 0).get s = ' '`
-/
@[inline] def Pos.Raw.nextUntil (s : String) (p : Char → Bool) (i : String.Pos.Raw) : String.Pos.Raw :=
  nextWhile s (fun c => !p c) i

@[deprecated Pos.Raw.nextUntil (since := "2025-10-10")]
def nextUntil (s : String) (p : Char → Bool) (i : String.Pos.Raw) : String.Pos.Raw :=
  i.nextUntil s p

/--
If {name}`pat` matches a prefix of {name}`s`, returns the remainder. Returns {name}`none` otherwise.

Use {name (scope := "Init.Data.String.Slice")}`String.dropPrefix` to return the slice
unchanged when {name}`pat` does not match a prefix.

This is a cheap operation because it does not allocate a new string to hold the result.
To convert the result into a string, use {name}`String.Slice.copy`.

This function is generic over all currently supported patterns.

Examples:
 * {lean}`"red green blue".dropPrefix? "red " == some "green blue".toSlice`
 * {lean}`"red green blue".dropPrefix? "reed " == none`
 * {lean}`"red green blue".dropPrefix? 'r' == some "ed green blue".toSlice`
 * {lean}`"red green blue".dropPrefix? Char.isLower == some "ed green blue".toSlice`
-/
def dropPrefix? (s : String) (pat : ρ) [ForwardPattern pat] : Option String.Slice :=
  s.toSlice.dropPrefix? pat

/--
If {name}`pat` matches a suffix of {name}`s`, returns the remainder. Returns {name}`none` otherwise.

Use {name (scope := "Init.Data.String.TakeDrop")}`String.dropSuffix` to return the slice
unchanged when {name}`pat` does not match a suffix.

This is a cheap operation because it does not allocate a new string to hold the result.
To convert the result into a string, use {name}`String.Slice.copy`.

This function is generic over all currently supported patterns.

Examples:
 * {lean}`"red green blue".dropSuffix? " blue" == some "red green".toSlice`
 * {lean}`"red green blue".dropSuffix? "bluu " == none`
 * {lean}`"red green blue".dropSuffix? 'e' == some "red green blu".toSlice`
 * {lean}`"red green blue".dropSuffix? Char.isLower == some "red green blu".toSlice`
-/
def dropSuffix? (s : String) (pat : ρ) [BackwardPattern pat] : Option String.Slice :=
  s.toSlice.dropSuffix? pat

/--
If {name}`pat` matches a prefix of {name}`s`, returns the remainder. Returns {name}`s` unmodified
otherwise.

Use {name}`String.dropPrefix?` to return {name}`none` when {name}`pat` does not match a prefix.

This is a cheap operation because it does not allocate a new string to hold the result.
To convert the result into a string, use {name}`String.Slice.copy`.

This function is generic over all currently supported patterns.

Examples:
 * {lean}`"red green blue".dropPrefix "red " == "green blue".toSlice`
 * {lean}`"red green blue".dropPrefix "reed " == "red green blue".toSlice`
 * {lean}`"red green blue".dropPrefix 'r' == "ed green blue".toSlice`
 * {lean}`"red green blue".dropPrefix Char.isLower == "ed green blue".toSlice`
-/
def dropPrefix (s : String) (pat : ρ) [ForwardPattern pat] : String.Slice :=
  s.toSlice.dropPrefix pat

@[deprecated String.dropPrefix (since := "2025-11-17")]
def stripPrefix (s pre : String) : String :=
  (s.dropPrefix pre).toString

@[deprecated Slice.dropPrefix (since := "2025-11-20")]
def Slice.stripPrefix (s pre : Slice) : Slice :=
  s.dropPrefix pre

/--
If {name}`pat` matches a suffix of {name}`s`, returns the remainder. Returns {name}`s` unmodified
otherwise.

Use {name}`String.dropSuffix?` to return {name}`none` when {name}`pat` does not match a prefix.

This is a cheap operation because it does not allocate a new string to hold the result.
To convert the result into a string, use {name}`String.Slice.copy`.

This function is generic over all currently supported patterns.

Examples:
 * {lean}`"red green blue".dropSuffix " blue" == "red green".toSlice`
 * {lean}`"red green blue".dropSuffix "bluu " == "red green blue".toSlice`
 * {lean}`"red green blue".dropSuffix 'e' == "red green blu".toSlice`
 * {lean}`"red green blue".dropSuffix Char.isLower == "red green blu".toSlice`
-/
def dropSuffix (s : String) (pat : ρ) [BackwardPattern pat] : String.Slice :=
  s.toSlice.dropSuffix pat

@[deprecated String.dropSuffix (since := "2025-11-17")]
def stripSuffix (s : String) (suff : String) : String :=
  (s.dropSuffix suff).toString

@[deprecated Slice.dropSuffix (since := "2025-11-20")]
def Slice.stripSuffix (s : Slice) (suff : Slice) : Slice :=
  s.dropSuffix suff

end String
