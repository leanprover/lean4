/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Init.Data.List.Basic
import Init.Data.Char.Basic
import Init.Data.Option.Basic
import Init.Data.String.Extern

universe u

namespace String

/-- Iterator over the characters (`Char`) of a `String`.

Typically created by `s.iter`, where `s` is a `String`.

An iterator is *valid* if the position `i` is *valid* for the string `s`, meaning `0 ≤ i ≤ s.endPos`
and `i` lies on a UTF8 byte boundary. If `i = s.endPos`, the iterator is at the end of the string.

Most operations on iterators return arbitrary values if the iterator is not valid. The functions in
the `String.Iterator` API should rule out the creation of invalid iterators, with two exceptions:

- `Iterator.next iter` is invalid if `iter` is already at the end of the string (`iter.atEnd` is
  `true`), and
- `Iterator.forward iter n`/`Iterator.nextn iter n` is invalid if `n` is strictly greater than the
  number of remaining characters.
-/
structure Iterator where
  /-- The string the iterator is for. -/
  s : String
  /-- The current position.

  This position is not necessarily valid for the string, for instance if one keeps calling
  `Iterator.next` when `Iterator.atEnd` is true. If the position is not valid, then the
  current character is `(default : Char)`, similar to `String.get` on an invalid position. -/
  i : Pos
  deriving DecidableEq

/-- Creates an iterator at the beginning of a string. -/
def mkIterator (s : String) : Iterator :=
  ⟨s, 0⟩

@[inherit_doc mkIterator]
abbrev iter := mkIterator

/-- The size of a string iterator is the number of bytes remaining. -/
instance : SizeOf String.Iterator where
  sizeOf i := i.1.utf8ByteSize - i.2.byteIdx

theorem Iterator.sizeOf_eq (i : String.Iterator) : sizeOf i = i.1.utf8ByteSize - i.2.byteIdx :=
  rfl

namespace Iterator
@[inherit_doc Iterator.s]
def toString := Iterator.s

/-- Number of bytes remaining in the iterator. -/
def remainingBytes : Iterator → Nat
  | ⟨s, i⟩ => s.endPos.byteIdx - i.byteIdx

@[inherit_doc Iterator.i]
def pos := Iterator.i

/-- The character at the current position.

On an invalid position, returns `(default : Char)`. -/
def curr : Iterator → Char
  | ⟨s, i⟩ => get s i

/-- Moves the iterator's position forward by one character, unconditionally.

It is only valid to call this function if the iterator is not at the end of the string, *i.e.*
`Iterator.atEnd` is `false`; otherwise, the resulting iterator will be invalid. -/
def next : Iterator → Iterator
  | ⟨s, i⟩ => ⟨s, s.next i⟩

/-- Decreases the iterator's position.

If the position is zero, this function is the identity. -/
def prev : Iterator → Iterator
  | ⟨s, i⟩ => ⟨s, s.prev i⟩

/-- True if the iterator is past the string's last character. -/
def atEnd : Iterator → Bool
  | ⟨s, i⟩ => i.byteIdx ≥ s.endPos.byteIdx

/-- True if the iterator is not past the string's last character. -/
def hasNext : Iterator → Bool
  | ⟨s, i⟩ => i.byteIdx < s.endPos.byteIdx

/-- True if the position is not zero. -/
def hasPrev : Iterator → Bool
  | ⟨_, i⟩ => i.byteIdx > 0

/-- Replaces the current character in the string.

Does nothing if the iterator is at the end of the string. If the iterator contains the only
reference to its string, this function will mutate the string in-place instead of allocating a new
one. -/
def setCurr : Iterator → Char → Iterator
  | ⟨s, i⟩, c => ⟨s.set i c, i⟩

/-- Moves the iterator's position to the end of the string.

Note that `i.toEnd.atEnd` is always `true`. -/
def toEnd : Iterator → Iterator
  | ⟨s, _⟩ => ⟨s, s.endPos⟩

/-- Extracts the substring between the positions of two iterators.

Returns the empty string if the iterators are for different strings, or if the position of the first
iterator is past the position of the second iterator. -/
def extract : Iterator → Iterator → String
  | ⟨s₁, b⟩, ⟨s₂, e⟩ =>
    if s₁ ≠ s₂ || b > e then ""
    else s₁.extract b e

/-- Moves the iterator's position several characters forward.

The resulting iterator is only valid if the number of characters to skip is less than or equal to
the number of characters left in the iterator. -/
def forward : Iterator → Nat → Iterator
  | it, 0   => it
  | it, n+1 => forward it.next n

/-- The remaining characters in an iterator, as a string. -/
def remainingToString : Iterator → String
  | ⟨s, i⟩ => s.extract i s.endPos

@[inherit_doc forward]
def nextn : Iterator → Nat → Iterator
  | it, 0   => it
  | it, i+1 => nextn it.next i

/-- Moves the iterator's position several characters back.

If asked to go back more characters than available, stops at the beginning of the string. -/
def prevn : Iterator → Nat → Iterator
  | it, 0   => it
  | it, i+1 => prevn it.prev i

end Iterator

end String
