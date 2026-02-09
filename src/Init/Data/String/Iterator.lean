/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Mario Carneiro
-/
module

prelude
public import Init.Data.String.Modify

/-!
# `String.Iterator`

This file contains `String.Iterator`, an outgoing API to be replaced by the iterator framework in
a future release.
-/

public section

namespace String.Legacy

/--
An iterator over the characters (Unicode code points) in a `String`. Typically created by
`String.iter`.

This is a no-longer-supported legacy API that will be removed in a future release. You should use
`String.Pos` instead, which is similar, but safer. To iterate over a string `s`, start with
`p : s.startPos`, advance it using `p.next`, access the current character using `p.get` and
check if the position is at the end using `p = s.endPos` or `p.IsAtEnd`.

String iterators pair a string with a valid byte index. This allows efficient character-by-character
processing of strings while avoiding the need to manually ensure that byte indices are used with the
correct strings.

An iterator is *valid* if the position `i` is *valid* for the string `s`, meaning `0 ≤ i ≤ s.rawEndPos`
and `i` lies on a UTF8 byte boundary. If `i = s.rawEndPos`, the iterator is at the end of the string.

Most operations on iterators return unspecified values if the iterator is not valid. The functions
in the `String.Iterator` API rule out the creation of invalid iterators, with two exceptions:
- `Iterator.next iter` is invalid if `iter` is already at the end of the string (`iter.atEnd` is
  `true`), and
- `Iterator.forward iter n`/`Iterator.nextn iter n` is invalid if `n` is strictly greater than the
  number of remaining characters.
-/
structure Iterator where
  /-- The string being iterated over. -/
  s : String
  /-- The current UTF-8 byte position in the string `s`.

  This position is not guaranteed to be valid for the string. If the position is not valid, then the
  current character is `(default : Char)`, similar to `String.get` on an invalid position.
  -/
  i : Pos.Raw
  deriving DecidableEq, Inhabited

/-- Creates an iterator at the beginning of the string.

This is a no-longer-supported legacy API that will be removed in a future release. You should use
`String.Pos` instead, which is similar, but safer. To iterate over a string `s`, start with
`p : s.startPos`, advance it using `p.next`, access the current character using `p.get` and
check if the position is at the end using `p = s.endPos` or `p.IsAtEnd`.
-/
@[inline] def mkIterator (s : String) : Iterator :=
  ⟨s, 0⟩

@[inherit_doc mkIterator]
abbrev iter := mkIterator

/--
The size of a string iterator is the number of bytes remaining.

Recursive functions that iterate towards the end of a string will typically decrease this measure.
-/
instance : SizeOf String.Legacy.Iterator where
  sizeOf i := i.1.utf8ByteSize - i.2.byteIdx

theorem Iterator.sizeOf_eq (i : String.Legacy.Iterator) : sizeOf i = i.1.utf8ByteSize - i.2.byteIdx :=
  rfl

namespace Iterator
@[inline, inherit_doc Iterator.s]
def toString := Iterator.s

/--
The number of UTF-8 bytes remaining in the iterator.
-/
@[inline] def remainingBytes : Iterator → Nat
  | ⟨s, i⟩ => s.rawEndPos.byteIdx - i.byteIdx

@[inline, inherit_doc Iterator.i]
def pos := Iterator.i

/--
Gets the character at the iterator's current position.

This is a no-longer-supported legacy API that will be removed in a future release. You should use
`String.Pos` instead, which is similar, but safer. To iterate over a string `s`, start with
`p : s.startPos`, advance it using `p.next`, access the current character using `p.get` and
check if the position is at the end using `p = s.endPos` or `p.IsAtEnd`.

A run-time bounds check is performed. Use `String.Iterator.curr'` to avoid redundant bounds checks.

If the position is invalid, returns `(default : Char)`.
-/
@[inline] def curr : Iterator → Char
  | ⟨s, i⟩ => i.get s

/--
Moves the iterator's position forward by one character, unconditionally.

This is a no-longer-supported legacy API that will be removed in a future release. You should use
`String.Pos` instead, which is similar, but safer. To iterate over a string `s`, start with
`p : s.startPos`, advance it using `p.next`, access the current character using `p.get` and
check if the position is at the end using `p = s.endPos` or `p.IsAtEnd`.

It is only valid to call this function if the iterator is not at the end of the string (i.e.
if `Iterator.atEnd` is `false`); otherwise, the resulting iterator will be invalid.
-/
@[inline] def next : Iterator → Iterator
  | ⟨s, i⟩ => ⟨s, i.next s⟩

/--
Moves the iterator's position backward by one character, unconditionally.

The position is not changed if the iterator is at the beginning of the string.
-/
@[inline] def prev : Iterator → Iterator
  | ⟨s, i⟩ => ⟨s, i.prev s⟩

/--
Checks whether the iterator is past its string's last character.
-/
@[inline] def atEnd : Iterator → Bool
  | ⟨s, i⟩ => i.byteIdx ≥ s.rawEndPos.byteIdx

/--
Checks whether the iterator is at or before the string's last character.
-/
@[inline] def hasNext : Iterator → Bool
  | ⟨s, i⟩ => i.byteIdx < s.rawEndPos.byteIdx

/--
Checks whether the iterator is after the beginning of the string.
-/
@[inline] def hasPrev : Iterator → Bool
  | ⟨_, i⟩ => i.byteIdx > 0

/--
Gets the character at the iterator's current position.

The proof of `it.hasNext` ensures that there is, in fact, a character at the current position. This
function is faster that `String.Iterator.curr` due to avoiding a run-time bounds check.
-/
@[inline] def curr' (it : Iterator) (h : it.hasNext) : Char :=
  match it with
  | ⟨s, i⟩ => i.get' s (by simpa only [hasNext, rawEndPos, decide_eq_true_eq, Pos.Raw.atEnd, ge_iff_le, Nat.not_le] using h)

/--
Moves the iterator's position forward by one character, unconditionally.

The proof of `it.hasNext` ensures that there is, in fact, a position that's one character forwards.
This function is faster that `String.Iterator.next` due to avoiding a run-time bounds check.
-/
@[inline] def next' (it : Iterator) (h : it.hasNext) : Iterator :=
  match it with
  | ⟨s, i⟩ => ⟨s, i.next' s (by simpa only [hasNext, rawEndPos, decide_eq_true_eq, Pos.Raw.atEnd, ge_iff_le, Nat.not_le] using h)⟩

/--
Moves the iterator's position to the end of the string, just past the last character.
-/
@[inline] def toEnd : Iterator → Iterator
  | ⟨s, _⟩ => ⟨s, s.rawEndPos⟩

/--
Extracts the substring between the positions of two iterators. The first iterator's position is the
start of the substring, and the second iterator's position is the end.

Returns the empty string if the iterators are for different strings, or if the position of the first
iterator is past the position of the second iterator.
-/
@[inline] def extract : Iterator → Iterator → String
  | ⟨s₁, b⟩, ⟨s₂, e⟩ =>
    if s₁ ≠ s₂ || b > e then ""
    else b.extract s₁ e

/--
Moves the iterator's position forward by the specified number of characters.

The resulting iterator is only valid if the number of characters to skip is less than or equal
to the number of characters left in the iterator.
-/
def forward : Iterator → Nat → Iterator
  | it, 0   => it
  | it, n+1 => forward it.next n

/--
The remaining characters in an iterator, as a string.
-/
@[inline] def remainingToString : Iterator → String
  | ⟨s, i⟩ => i.extract s s.rawEndPos

@[inherit_doc forward]
def nextn : Iterator → Nat → Iterator
  | it, 0   => it
  | it, i+1 => nextn it.next i

/--
Moves the iterator's position back by the specified number of characters, stopping at the beginning
of the string.
-/
def prevn : Iterator → Nat → Iterator
  | it, 0   => it
  | it, i+1 => prevn it.prev i

theorem sizeOf_next_lt_of_hasNext (i : String.Legacy.Iterator) (h : i.hasNext) : sizeOf i.next < sizeOf i := by
  cases i; rename_i s pos; simp [Iterator.next, Iterator.sizeOf_eq]; simp [Iterator.hasNext] at h
  exact Nat.sub_lt_sub_left h (String.Pos.Raw.lt_next s pos)

macro_rules
| `(tactic| decreasing_trivial) =>
  `(tactic| with_reducible apply String.Legacy.Iterator.sizeOf_next_lt_of_hasNext; assumption)

theorem sizeOf_next_lt_of_atEnd (i : String.Legacy.Iterator) (h : ¬ i.atEnd = true) : sizeOf i.next < sizeOf i :=
  have h : i.hasNext := decide_eq_true <| Nat.gt_of_not_le <| mt decide_eq_true h
  sizeOf_next_lt_of_hasNext i h

macro_rules
| `(tactic| decreasing_trivial) =>
  `(tactic| with_reducible apply String.Legacy.Iterator.sizeOf_next_lt_of_atEnd; assumption)

/--
Replaces the current character in the string.

Does nothing if the iterator is at the end of the string. If both the replacement character and the
replaced character are 7-bit ASCII characters and the string is not shared, then it is updated
in-place and not copied.
-/
@[inline] def setCurr : Iterator → Char → Iterator
  | ⟨s, i⟩, c => ⟨i.set s c, i⟩

/--
Moves the iterator forward until the Boolean predicate `p` returns `true` for the iterator's current
character or until the end of the string is reached. Does nothing if the current character already
satisfies `p`.
-/
@[specialize] def find (it : Iterator) (p : Char → Bool) : Iterator :=
  if it.atEnd then it
  else if p it.curr then it
  else find it.next p

/--
Iterates over a string, updating a state at each character using the provided function `f`, until
`f` returns `none`. Begins with the state `init`. Returns the state and character for which `f`
returns `none`.
-/
@[specialize] def foldUntil (it : Iterator) (init : α) (f : α → Char → Option α) : α × Iterator :=
  if it.atEnd then
    (init, it)
  else if let some a := f init it.curr then
    foldUntil it.next a f
  else
    (init, it)

end Iterator

end String.Legacy

namespace Substring.Raw

/--
Returns an iterator into the underlying string, at the substring's starting position. The ending
position is discarded, so the iterator alone cannot be used to determine whether its current
position is within the original substring.
-/
@[inline] def toLegacyIterator : Substring.Raw → String.Legacy.Iterator
  | ⟨s, b, _⟩ => ⟨s, b⟩


end Substring.Raw

instance : Repr String.Legacy.Iterator where
  reprPrec | ⟨s, pos⟩, prec => Repr.addAppParen ("String.Iterator.mk " ++ reprArg s ++ " " ++ reprArg pos) prec

instance : ToString String.Legacy.Iterator :=
  ⟨fun it => it.remainingToString⟩

section Deprecations

@[deprecated String.Legacy.Iterator (since := "2025-11-12")]
abbrev String.Iterator := String.Legacy.Iterator
@[deprecated String.Legacy.iter (since := "2025-11-12")]
abbrev String.iter := String.Legacy.iter
@[deprecated String.Legacy.mkIterator (since := "2025-11-12")]
abbrev String.mkIterator := String.Legacy.mkIterator
@[deprecated String.Legacy.Iterator.curr (since := "2025-11-12")]
abbrev String.Iterator.curr := String.Legacy.Iterator.curr
@[deprecated String.Legacy.Iterator.next (since := "2025-11-12")]
abbrev String.Iterator.next := String.Legacy.Iterator.next
@[deprecated String.Legacy.Iterator.hasNext (since := "2025-11-12")]
abbrev String.Iterator.hasNext := String.Legacy.Iterator.hasNext
@[deprecated Substring.Raw.toLegacyIterator (since := "2025-11-12")]
abbrev Substring.toIterator := Substring.Raw.toLegacyIterator

end Deprecations
