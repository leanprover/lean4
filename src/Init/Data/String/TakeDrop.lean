/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Mario Carneiro
-/
module

prelude
public import Init.Data.String.Substring

/-!
# `String.take` and variants

This file contains the implementations of `String.take` and its variants. Currently, they are
implemented in terms of `Substring`; soon, they will be implemented in terms of `String.Slice`
instead.
-/

public section

namespace String

/--
Removes the specified number of characters (Unicode code points) from the start of the string.

If `n` is greater than `s.length`, returns `""`.

Examples:
 * `"red green blue".drop 4 = "green blue"`
 * `"red green blue".drop 10 = "blue"`
 * `"red green blue".drop 50 = ""`
-/
@[inline] def drop (s : String) (n : Nat) : String :=
  (s.toRawSubstring.drop n).toString

@[export lean_string_drop]
def Internal.dropImpl (s : String) (n : Nat) : String :=
  String.drop s n

/--
Removes the specified number of characters (Unicode code points) from the end of the string.

If `n` is greater than `s.length`, returns `""`.

Examples:
 * `"red green blue".dropRight 5 = "red green"`
 * `"red green blue".dropRight 11 = "red"`
 * `"red green blue".dropRight 50 = ""`
-/
@[inline] def dropRight (s : String) (n : Nat) : String :=
  (s.toRawSubstring.dropRight n).toString

@[export lean_string_dropright]
def Internal.dropRightImpl (s : String) (n : Nat) : String :=
  String.dropRight s n

/--
Creates a new string that contains the first `n` characters (Unicode code points) of `s`.

If `n` is greater than `s.length`, returns `s`.

Examples:
* `"red green blue".take 3 = "red"`
* `"red green blue".take 1 = "r"`
* `"red green blue".take 0 = ""`
* `"red green blue".take 100 = "red green blue"`
-/
@[inline] def take (s : String) (n : Nat) : String :=
  (s.toRawSubstring.take n).toString

/--
Creates a new string that contains the last `n` characters (Unicode code points) of `s`.

If `n` is greater than `s.length`, returns `s`.

Examples:
* `"red green blue".takeRight 4 = "blue"`
* `"red green blue".takeRight 1 = "e"`
* `"red green blue".takeRight 0 = ""`
* `"red green blue".takeRight 100 = "red green blue"`
-/
@[inline] def takeRight (s : String) (n : Nat) : String :=
  (s.toRawSubstring.takeRight n).toString

/--
Creates a new string that contains the longest prefix of `s` in which `p` returns `true` for all
characters.

Examples:
* `"red green blue".takeWhile (·.isLetter) = "red"`
* `"red green blue".takeWhile (· == 'r') = "r"`
* `"red green blue".takeWhile (· != 'n') = "red gree"`
* `"red green blue".takeWhile (fun _ => true) = "red green blue"`
-/
@[inline] def takeWhile (s : String) (p : Char → Bool) : String :=
  (s.toRawSubstring.takeWhile p).toString

/--
Creates a new string by removing the longest prefix from `s` in which `p` returns `true` for all
characters.

Examples:
* `"red green blue".dropWhile (·.isLetter) = " green blue"`
* `"red green blue".dropWhile (· == 'r') = "ed green blue"`
* `"red green blue".dropWhile (· != 'n') = "n blue"`
* `"red green blue".dropWhile (fun _ => true) = ""`
-/
@[inline] def dropWhile (s : String) (p : Char → Bool) : String :=
  (s.toRawSubstring.dropWhile p).toString

/--
Creates a new string that contains the longest suffix of `s` in which `p` returns `true` for all
characters.

Examples:
* `"red green blue".takeRightWhile (·.isLetter) = "blue"`
* `"red green blue".takeRightWhile (· == 'e') = "e"`
* `"red green blue".takeRightWhile (· != 'n') = " blue"`
* `"red green blue".takeRightWhile (fun _ => true) = "red green blue"`
-/
@[inline] def takeRightWhile (s : String) (p : Char → Bool) : String :=
  (s.toRawSubstring.takeRightWhile p).toString

/--
Creates a new string by removing the longest suffix from `s` in which `p` returns `true` for all
characters.

Examples:
* `"red green blue".dropRightWhile (·.isLetter) = "red green "`
* `"red green blue".dropRightWhile (· == 'e') = "red green blu"`
* `"red green blue".dropRightWhile (· != 'n') = "red green"`
* `"red green blue".dropRightWhile (fun _ => true) = ""`
-/
@[inline] def dropRightWhile (s : String) (p : Char → Bool) : String :=
  (s.toRawSubstring.dropRightWhile p).toString

/--
Checks whether the first string (`s`) begins with the second (`pre`).

`String.isPrefix` is a version that takes the potential prefix before the string.

Examples:
 * `"red green blue".startsWith "red" = true`
 * `"red green blue".startsWith "green" = false`
 * `"red green blue".startsWith "" = true`
 * `"red".startsWith "red" = true`
-/
@[inline] def startsWith (s pre : String) : Bool :=
  s.toRawSubstring.take pre.length == pre.toRawSubstring

/--
Checks whether the first string (`s`) ends with the second (`post`).

Examples:
 * `"red green blue".endsWith "blue" = true`
 * `"red green blue".endsWith "green" = false`
 * `"red green blue".endsWith "" = true`
 * `"red".endsWith "red" = true`
-/
@[inline] def endsWith (s post : String) : Bool :=
  s.toRawSubstring.takeRight post.length == post.toRawSubstring

/--
Removes trailing whitespace from a string.

“Whitespace” is defined as characters for which `Char.isWhitespace` returns `true`.

Examples:
* `"abc".trimRight = "abc"`
* `"   abc".trimRight = "   abc"`
* `"abc \t  ".trimRight = "abc"`
* `"  abc   ".trimRight = "  abc"`
* `"abc\ndef\n".trimRight = "abc\ndef"`
-/
@[inline] def trimRight (s : String) : String :=
  s.toRawSubstring.trimRight.toString

/--
Removes leading whitespace from a string.

“Whitespace” is defined as characters for which `Char.isWhitespace` returns `true`.

Examples:
* `"abc".trimLeft = "abc"`
* `"   abc".trimLeft = "   abc"`
* `"abc \t  ".trimLeft = "abc \t  "`
* `"  abc   ".trimLeft = "abc   "`
* `"abc\ndef\n".trimLeft = "abc\ndef\n"`
-/
@[inline] def trimLeft (s : String) : String :=
  s.toRawSubstring.trimLeft.toString

/--
Removes leading and trailing whitespace from a string.

“Whitespace” is defined as characters for which `Char.isWhitespace` returns `true`.

Examples:
* `"abc".trim = "abc"`
* `"   abc".trim = "abc"`
* `"abc \t  ".trim = "abc"`
* `"  abc   ".trim = "abc"`
* `"abc\ndef\n".trim = "abc\ndef"`
-/
@[inline] def trim (s : String) : String :=
  s.toRawSubstring.trim.toString

@[export lean_string_trim]
def Internal.trimImpl (s : String) : String :=
  String.trim s

/--
Repeatedly increments a position in a string, as if by `String.next`, while the predicate `p`
returns `true` for the character at the position. Stops incrementing at the end of the string or
when `p` returns `false` for the current character.

Examples:
* `let s := "   a  "; s.get (s.nextWhile Char.isWhitespace 0) = 'a'`
* `let s := "a  "; s.get (s.nextWhile Char.isWhitespace 0) = 'a'`
* `let s := "ba  "; s.get (s.nextWhile Char.isWhitespace 0) = 'b'`
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
Repeatedly increments a position in a string, as if by `String.next`, while the predicate `p`
returns `false` for the character at the position. Stops incrementing at the end of the string or
when `p` returns `true` for the current character.

Examples:
* `let s := "   a  "; s.get (s.nextUntil Char.isWhitespace 0) = ' '`
* `let s := "   a  "; s.get (s.nextUntil Char.isLetter 0) = 'a'`
* `let s := "a  "; s.get (s.nextUntil Char.isWhitespace 0) = ' '`
-/
@[inline] def Pos.Raw.nextUntil (s : String) (p : Char → Bool) (i : String.Pos.Raw) : String.Pos.Raw :=
  nextWhile s (fun c => !p c) i

@[deprecated Pos.Raw.nextUntil (since := "2025-10-10")]
def nextUntil (s : String) (p : Char → Bool) (i : String.Pos.Raw) : String.Pos.Raw :=
  i.nextUntil s p

/--
If `pre` is a prefix of `s`, returns the remainder. Returns `none` otherwise.

The string `pre` is a prefix of `s` if there exists a `t : String` such that `s = pre ++ t`. If so,
the result is `some t`.

Use `String.stripPrefix` to return the string unchanged when `pre` is not a prefix.

Examples:
 * `"red green blue".dropPrefix? "red " = some "green blue"`
 * `"red green blue".dropPrefix? "reed " = none`
 * `"red green blue".dropPrefix? "" = some "red green blue"`
-/
def dropPrefix? (s : String) (pre : String) : Option Substring.Raw :=
  s.toRawSubstring.dropPrefix? pre.toRawSubstring

/--
If `suff` is a suffix of `s`, returns the remainder. Returns `none` otherwise.

The string `suff` is a suffix of `s` if there exists a `t : String` such that `s = t ++ suff`. If so,
the result is `some t`.

Use `String.stripSuffix` to return the string unchanged when `suff` is not a suffix.

Examples:
 * `"red green blue".dropSuffix? " blue" = some "red green"`
 * `"red green blue".dropSuffix? " blu " = none`
 * `"red green blue".dropSuffix? "" = some "red green blue"`
-/
def dropSuffix? (s : String) (suff : String) : Option Substring.Raw :=
  s.toRawSubstring.dropSuffix? suff.toRawSubstring

/--
If `pre` is a prefix of `s`, returns the remainder. Returns `s` unmodified otherwise.

The string `pre` is a prefix of `s` if there exists a `t : String` such that `s = pre ++ t`. If so,
the result is `t`. Otherwise, it is `s`.

Use `String.dropPrefix?` to return `none` when `pre` is not a prefix.

Examples:
 * `"red green blue".stripPrefix "red " = "green blue"`
 * `"red green blue".stripPrefix "reed " = "red green blue"`
 * `"red green blue".stripPrefix "" = "red green blue"`
-/
def stripPrefix (s : String) (pre : String) : String :=
  s.dropPrefix? pre |>.map Substring.Raw.toString |>.getD s

/--
If `suff` is a suffix of `s`, returns the remainder. Returns `s` unmodified otherwise.

The string `suff` is a suffix of `s` if there exists a `t : String` such that `s = t ++ suff`. If so,
the result is `t`. Otherwise, it is `s`.

Use `String.dropSuffix?` to return `none` when `suff` is not a suffix.

Examples:
 * `"red green blue".stripSuffix " blue" = "red green"`
 * `"red green blue".stripSuffix " blu " = "red green blue"`
 * `"red green blue".stripSuffix "" = "red green blue"`
-/
def stripSuffix (s : String) (suff : String) : String :=
  s.dropSuffix? suff |>.map Substring.Raw.toString |>.getD s

end String
