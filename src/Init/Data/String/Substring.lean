/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Mario Carneiro
-/
module

prelude
public import Init.Data.String.Slice

/-!
# The `Substring` type

This file contains API for `Substring` type, which is a legacy API that will be replaced by the
safer variant `String.Slice`.
-/

public section

namespace Substring.Raw

/--
Converts a `String.Slice` into a `Substring.Raw`.
-/
@[inline]
def ofSlice (s : String.Slice) : Substring.Raw where
  str := s.str
  startPos := s.startInclusive.offset
  stopPos := s.endExclusive.offset

/--
Converts a `Substring.Raw` into a `String.Slice`, returning `none` if the substring is invalid.
-/
@[inline]
def toSlice? (s : Substring.Raw) : Option String.Slice :=
  if h : s.startPos.IsValid s.str ∧ s.stopPos.IsValid s.str ∧ s.startPos ≤ s.stopPos then
    some (String.Slice.mk s.str (s.str.pos s.startPos h.1) (s.str.pos s.stopPos h.2.1)
      (by simp [String.Pos.le_iff, h.2.2]))
  else
    none

/--
Checks whether a substring is empty.

A substring is empty if its start and end positions are the same.
-/
@[inline] def isEmpty (ss : Substring.Raw) : Bool :=
  ss.bsize == 0

@[export lean_substring_isempty]
def Internal.isEmptyImpl (ss : Substring.Raw) : Bool :=
  Substring.Raw.isEmpty ss

/--{}
Copies the region of the underlying string pointed to by a substring into a fresh string.
-/
@[inline] def toString : Substring.Raw → String
  | ⟨s, b, e⟩ => b.extract s e

@[export lean_substring_tostring]
def Internal.toStringImpl : Substring.Raw → String :=
  Substring.Raw.toString

/--
Returns the character at the given position in the substring.

The position is relative to the substring, rather than the underlying string, and no bounds checking
is performed with respect to the substring's end position. If the relative position is not a valid
position in the underlying string, the fallback value `(default : Char)`, which is `'A'`, is
returned.  Does not panic.
-/
@[inline] def get : Substring.Raw → String.Pos.Raw → Char
  | ⟨s, b, _⟩, p => (p.offsetBy b).get s

@[export lean_substring_get]
def Internal.getImpl : Substring.Raw → String.Pos.Raw → Char :=
  Substring.Raw.get

/--
Returns the next position in a substring after the given position. If the position is at the end of
the substring, it is returned unmodified.

Both the input position and the returned position are interpreted relative to the substring's start
position, not the underlying string.
-/
@[inline] def next : Substring.Raw → String.Pos.Raw → String.Pos.Raw
  | ⟨s, b, e⟩, p =>
    let absP := p.offsetBy b
    if absP = e then p else { byteIdx := (absP.next s).byteIdx - b.byteIdx }

theorem lt_next (s : Substring.Raw) (i : String.Pos.Raw) (h : i.1 < s.bsize) :
    i.1 < (s.next i).1 := by
  simp [next]; rw [if_neg ?a]
  case a =>
    refine mt (congrArg String.Pos.Raw.byteIdx) (Nat.ne_of_lt ?_)
    exact (Nat.add_comm .. ▸ Nat.add_lt_of_lt_sub h :)
  apply Nat.lt_sub_of_add_lt
  rw [Nat.add_comm]; apply String.Pos.Raw.lt_next

/--
Returns the previous position in a substring, just prior to the given position. If the position is
at the beginning of the substring, it is returned unmodified.

Both the input position and the returned position are interpreted relative to the substring's start
position, not the underlying string.
-/
@[inline] def prev : Substring.Raw → String.Pos.Raw → String.Pos.Raw
  | ⟨s, b, _⟩, p =>
    let absP := p.offsetBy b
    if absP = b then p else { byteIdx := (absP.prev s).byteIdx - b.byteIdx }

@[export lean_substring_prev]
def Internal.prevImpl : Substring.Raw → String.Pos.Raw → String.Pos.Raw :=
  Substring.Raw.prev

/--
Returns the position that's the specified number of characters forward from the given position in a
substring. If the end position of the substring is reached, it is returned.

Both the input position and the returned position are interpreted relative to the substring's start
position, not the underlying string.
-/
def nextn : Substring.Raw → Nat → String.Pos.Raw → String.Pos.Raw
  | _,  0,   p => p
  | ss, i+1, p => ss.nextn i (ss.next p)

/--
Returns the position that's the specified number of characters prior to the given position in a
substring. If the start position of the substring is reached, it is returned.

Both the input position and the returned position are interpreted relative to the substring's start
position, not the underlying string.
-/
def prevn : Substring.Raw → Nat → String.Pos.Raw → String.Pos.Raw
  | _,  0,   p => p
  | ss, i+1, p => ss.prevn i (ss.prev p)

/--
Returns the first character in the substring.

If the substring is empty, but the substring's start position is a valid position in the underlying
string, then the character at the start position is returned. If the substring's start position is
not a valid position in the string, the fallback value `(default : Char)`, which is `'A'`, is
returned.  Does not panic.
-/
@[inline, expose] def front (s : Substring.Raw) : Char :=
  s.get 0

@[export lean_substring_front]
def Internal.frontImpl : Substring.Raw → Char :=
  Substring.Raw.front

/--
Returns the substring-relative position of the first occurrence of `c` in `s`, or `s.bsize` if `c`
doesn't occur.
-/
@[inline] def posOf (s : Substring.Raw) (c : Char) : String.Pos.Raw :=
  s.toSlice?.map (·.find c |>.offset) |>.getD ⟨s.bsize⟩

/--
Removes the specified number of characters (Unicode code points) from the beginning of a substring
by advancing its start position.

If the substring's end position is reached, the start position is not advanced past it.
-/
@[inline] def drop : Substring.Raw → Nat → Substring.Raw
  | ss@⟨s, b, e⟩, n => ⟨s, (ss.nextn n 0).offsetBy b, e⟩

@[export lean_substring_drop]
def Internal.dropImpl : Substring.Raw → Nat → Substring.Raw :=
  Substring.Raw.drop

/--
Removes the specified number of characters (Unicode code points) from the end of a substring
by moving its end position towards its start position.

If the substring's start position is reached, the end position is not retracted past it.
-/
@[inline] def dropRight : Substring.Raw → Nat → Substring.Raw
  | ss@⟨s, b, _⟩, n => ⟨s, b, (ss.prevn n ⟨ss.bsize⟩).offsetBy b⟩

/--
Retains only the specified number of characters (Unicode code points) at the beginning of a
substring, by moving its end position towards its start position.

If the substring's start position is reached, the end position is not retracted past it.
-/
@[inline] def take : Substring.Raw → Nat → Substring.Raw
  | ss@⟨s, b, _⟩, n => ⟨s, b, (ss.nextn n 0).offsetBy b⟩

/--
Retains only the specified number of characters (Unicode code points) at the end of a substring, by
moving its start position towards its end position.

If the substring's end position is reached, the start position is not advanced past it.
-/
@[inline] def takeRight : Substring.Raw → Nat → Substring.Raw
  | ss@⟨s, b, e⟩, n => ⟨s, (ss.prevn n ⟨ss.bsize⟩).offsetBy b, e⟩

/--
Checks whether a position in a substring is precisely equal to its ending position.

The position is understood relative to the substring's starting position, rather than the underlying
string's starting position.
-/
@[inline] def atEnd : Substring.Raw → String.Pos.Raw → Bool
  | ⟨_, b, e⟩, p => p.offsetBy b == e

/--
Returns the region of the substring delimited by the provided start and stop positions, as a
substring. The positions are interpreted with respect to the substring's start position, rather than
the underlying string.

If the resulting substring is empty, then the resulting substring is a substring of the empty string
`""`. Otherwise, the underlying string is that of the input substring with the beginning and end
positions adjusted.
-/
@[inline] def extract : Substring.Raw → String.Pos.Raw → String.Pos.Raw → Substring.Raw
  | ⟨s, b, e⟩, b', e' => if b' ≥ e' then ⟨"", 0, 0⟩ else ⟨s, e.min (b'.offsetBy b), e.min (e'.offsetBy b)⟩

@[export lean_substring_extract]
def Internal.extractImpl : Substring.Raw → String.Pos.Raw → String.Pos.Raw → Substring.Raw :=
  Substring.Raw.extract

/--
Splits a substring `s` on occurrences of the separator string `sep`. The default separator is `" "`.

When `sep` is empty, the result is `[s]`. When `sep` occurs in overlapping patterns, the first match
is taken. There will always be exactly `n+1` elements in the returned list if there were `n`
non-overlapping matches of `sep` in the string. The separators are not included in the returned
substrings, which are all substrings of `s`'s string.
-/
def splitOn (s : Substring.Raw) (sep : String := " ") : List Substring.Raw :=
  if sep == "" then
    [s]
  else
    let rec loop (b i j : String.Pos.Raw) (r : List Substring.Raw) : List Substring.Raw :=
      if h : i.byteIdx < s.bsize then
        have := Nat.sub_lt_sub_left h (lt_next s i h)
        if s.get i == j.get sep then
          let i := s.next i
          let j := j.next sep
          if j.atEnd sep then
            loop i i 0 (s.extract b (i.unoffsetBy j) :: r)
          else
            loop b i j r
        else
          loop b (s.next i) 0 r
      else
        let r := if j.atEnd sep then
          "".toRawSubstring :: s.extract b (i.unoffsetBy j) :: r
        else
          s.extract b i :: r
        r.reverse
      termination_by s.bsize - i.1
    loop 0 0 0 []

/--
Folds a function over a substring from the left, accumulating a value starting with `init`. The
accumulated value is combined with each character in order, using `f`.
-/
@[inline] def foldl {α : Type u} (f : α → Char → α) (init : α) (s : Substring.Raw) : α :=
  s.toSlice?.get!.foldl f init

/--
Folds a function over a substring from the right, accumulating a value starting with `init`. The
accumulated value is combined with each character in reverse order, using `f`.
-/
@[inline] def foldr {α : Type u} (f : Char → α → α) (init : α) (s : Substring.Raw) : α :=
  s.toSlice?.get!.foldr f init

/--
Checks whether the Boolean predicate `p` returns `true` for any character in a substring.

Short-circuits at the first character for which `p` returns `true`.
-/
@[inline, suggest_for Substring.Raw.some] def any (s : Substring.Raw) (p : Char → Bool) : Bool :=
  s.toSlice?.get!.any p

/--
Checks whether the Boolean predicate `p` returns `true` for every character in a substring.

Short-circuits at the first character for which `p` returns `false`.
-/
@[inline, suggest_for Substring.Raw.every] def all (s : Substring.Raw) (p : Char → Bool) : Bool :=
  s.toSlice?.get!.all p

@[export lean_substring_all]
def Internal.allImpl (s : Substring.Raw) (p : Char → Bool) : Bool :=
  Substring.Raw.all s p

/--
Checks whether a substring contains the specified character.
-/
@[inline] def contains (s : Substring.Raw) (c : Char) : Bool :=
  s.any (fun a => a == c)

@[specialize] def takeWhileAux (s : String) (stopPos : String.Pos.Raw) (p : Char → Bool) (i : String.Pos.Raw) : String.Pos.Raw :=
  if h : i < stopPos then
    if p (i.get s) then
      have := Nat.sub_lt_sub_left h (String.Pos.Raw.lt_next s i)
      takeWhileAux s stopPos p (i.next s)
    else i
  else i
termination_by stopPos.1 - i.1

/--
Retains only the longest prefix of a substring in which a Boolean predicate returns `true` for all
characters by moving the substring's end position towards its start position.
-/
@[inline] def takeWhile : Substring.Raw → (Char → Bool) → Substring.Raw
  | ⟨s, b, e⟩, p =>
    let e := takeWhileAux s e p b;
    ⟨s, b, e⟩

@[export lean_substring_takewhile]
def Internal.takeWhileImpl : Substring.Raw → (Char → Bool) → Substring.Raw :=
  Substring.Raw.takeWhile

/--
Removes the longest prefix of a substring in which a Boolean predicate returns `true` for all
characters by moving the substring's start position. The start position is moved to the position of
the first character for which the predicate returns `false`, or to the substring's end position if
the predicate always returns `true`.
-/
@[inline] def dropWhile : Substring.Raw → (Char → Bool) → Substring.Raw
  | ⟨s, b, e⟩, p =>
    let b := takeWhileAux s e p b;
    ⟨s, b, e⟩

@[specialize] def takeRightWhileAux (s : String) (begPos : String.Pos.Raw) (p : Char → Bool) (i : String.Pos.Raw) : String.Pos.Raw :=
  if h : begPos < i then
    have := String.Pos.Raw.prev_lt_of_pos s i <| mt (congrArg String.Pos.Raw.byteIdx) <|
      Ne.symm <| Nat.ne_of_lt <| Nat.lt_of_le_of_lt (Nat.zero_le _) h
    let i' := i.prev s
    let c  := i'.get s
    if !p c then i
    else takeRightWhileAux s begPos p i'
  else i
termination_by i.1

/--
Retains only the longest suffix of a substring in which a Boolean predicate returns `true` for all
characters by moving the substring's start position towards its end position.
-/
@[inline] def takeRightWhile : Substring.Raw → (Char → Bool) → Substring.Raw
  | ⟨s, b, e⟩, p =>
    let b := takeRightWhileAux s b p e
    ⟨s, b, e⟩

/--
Removes the longest suffix of a substring in which a Boolean predicate returns `true` for all
characters by moving the substring's end position. The end position is moved just after the position
of the last character for which the predicate returns `false`, or to the substring's start position
if the predicate always returns `true`.
-/
@[inline] def dropRightWhile : Substring.Raw → (Char → Bool) → Substring.Raw
  | ⟨s, b, e⟩, p =>
    let e := takeRightWhileAux s b p e
    ⟨s, b, e⟩

/--
Removes leading whitespace from a substring by moving its start position to the first non-whitespace
character, or to its end position if there is no non-whitespace character.

“Whitespace” is defined as characters for which `Char.isWhitespace` returns `true`.
-/
@[inline] def trimLeft (s : Substring.Raw) : Substring.Raw :=
  s.dropWhile Char.isWhitespace

/--
Removes trailing whitespace from a substring by moving its end position to the last non-whitespace
character, or to its start position if there is no non-whitespace character.

“Whitespace” is defined as characters for which `Char.isWhitespace` returns `true`.
-/
@[inline] def trimRight (s : Substring.Raw) : Substring.Raw :=
  s.dropRightWhile Char.isWhitespace

/--
Removes leading and trailing whitespace from a substring by first moving its start position to the
first non-whitespace character, and then moving its end position to the last non-whitespace
character.

If the substring consists only of whitespace, then the resulting substring's start position is moved
to its end position.

“Whitespace” is defined as characters for which `Char.isWhitespace` returns `true`.

Examples:
 * `" red green blue ".toRawSubstring.trim.toString = "red green blue"`
 * `" red green blue ".toRawSubstring.trim.startPos = ⟨1⟩`
 * `" red green blue ".toRawSubstring.trim.stopPos = ⟨15⟩`
 * `"     ".toRawSubstring.trim.startPos = ⟨5⟩`
-/
@[inline] def trim : Substring.Raw → Substring.Raw
  | ⟨s, b, e⟩ =>
    let b := takeWhileAux s e Char.isWhitespace b
    let e := takeRightWhileAux s b Char.isWhitespace e
    ⟨s, b, e⟩

/--
Checks whether the substring can be interpreted as the decimal representation of a natural number.

A substring can be interpreted as a decimal natural number if it is not empty and all the characters
in it are digits. Underscores ({lit}`_`) are allowed as digit separators for readability, but cannot appear
at the start, at the end, or consecutively.

Use `Substring.toNat?` to convert such a substring to a natural number.
-/
@[inline] def isNat (s : Substring.Raw) : Bool :=
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
Checks whether the substring can be interpreted as the decimal representation of a natural number,
returning the number if it can.

A substring can be interpreted as a decimal natural number if it is not empty and all the characters
in it are digits. Underscores ({lit}`_`) are allowed as digit separators and are ignored during parsing.

Use `Substring.isNat` to check whether the substring is such a substring.
-/
def toNat? (s : Substring.Raw) : Option Nat :=
  if s.isNat then
    some <| s.foldl (fun n c => if c = '_' then n else n*10 + (c.toNat - '0'.toNat)) 0
  else
    none

/--
Given a `Substring`, returns another one which has valid endpoints
and represents the same substring according to `Substring.toString`.
(Note, the substring may still be inverted, i.e. beginning greater than end.)
-/
def repair : Substring.Raw → Substring.Raw
  | ⟨s, b, e⟩ => ⟨s, if b.isValid s then b else s.rawEndPos, if e.isValid s then e else s.rawEndPos⟩

/--
Checks whether two substrings represent equal strings. Usually accessed via the `==` operator.

Two substrings do not need to have the same underlying string or the same start and end positions;
instead, they are equal if they contain the same sequence of characters.
-/
def beq (ss1 ss2 : Substring.Raw) : Bool :=
  let ss1 := ss1.repair
  let ss2 := ss2.repair
  ss1.bsize == ss2.bsize && String.Pos.Raw.substrEq ss1.str ss1.startPos ss2.str ss2.startPos ss1.bsize

@[export lean_substring_beq]
def Internal.beqImpl (ss1 ss2 : Substring.Raw) : Bool :=
  Substring.Raw.beq ss1 ss2

instance hasBeq : BEq Substring.Raw := ⟨beq⟩

/--
Checks whether two substrings have the same position and content.

The two substrings do not need to have the same underlying string for this check to succeed.
-/
def sameAs (ss1 ss2 : Substring.Raw) : Bool :=
  ss1.startPos == ss2.startPos && ss1 == ss2

/--
Returns the longest common prefix of two substrings.

The returned substring uses the same underlying string as `s`.
-/
def commonPrefix (s t : Substring.Raw) : Substring.Raw :=
  { s with stopPos := loop s.startPos t.startPos }
where
  /-- Returns the ending position of the common prefix, working up from `spos, tpos`. -/
  loop spos tpos :=
    if h : spos < s.stopPos ∧ tpos < t.stopPos then
      if spos.get s.str == tpos.get t.str then
        have := Nat.sub_lt_sub_left h.1 (String.Pos.Raw.lt_next s.str spos)
        loop (spos.next s.str) (tpos.next t.str)
      else
        spos
    else
      spos
  termination_by s.stopPos.byteIdx - spos.byteIdx

/--
Returns the longest common suffix of two substrings.

The returned substring uses the same underlying string as `s`.
-/
def commonSuffix (s t : Substring.Raw) : Substring.Raw :=
  { s with startPos := loop s.stopPos t.stopPos }
where
  /-- Returns the starting position of the common prefix, working down from `spos, tpos`. -/
  loop spos tpos :=
    if h : s.startPos < spos ∧ t.startPos < tpos then
      let spos' := spos.prev s.str
      let tpos' := tpos.prev t.str
      if spos'.get s.str == tpos'.get t.str then
        have : spos' < spos := String.Pos.Raw.prev_lt_of_pos s.str spos (String.Pos.Raw.ne_zero_of_lt h.1)
        loop spos' tpos'
      else
        spos
    else
      spos
  termination_by spos.byteIdx

/--
If `pre` is a prefix of `s`, returns the remainder. Returns `none` otherwise.

The substring `pre` is a prefix of `s` if there exists a `t : Substring` such that
`s.toString = pre.toString ++ t.toString`. If so, the result is the substring of `s` without the
prefix.
-/
def dropPrefix? (s : Substring.Raw) (pre : Substring.Raw) : Option Substring.Raw :=
  let t := s.commonPrefix pre
  if t.bsize = pre.bsize then
    some { s with startPos := t.stopPos }
  else
    none

/--
If `suff` is a suffix of `s`, returns the remainder. Returns `none` otherwise.

The substring `suff` is a suffix of `s` if there exists a `t : Substring` such that
`s.toString = t.toString ++ suff.toString`. If so, the result the substring of `s` without the
suffix.
-/
def dropSuffix? (s : Substring.Raw) (suff : Substring.Raw) : Option Substring.Raw :=
  let t := s.commonSuffix suff
  if t.bsize = suff.bsize then
    some { s with stopPos := t.startPos }
  else
    none

@[simp] theorem prev_zero (s : Substring.Raw) : s.prev 0 = 0 := by simp [prev]

@[simp] theorem prevn_zero (s : Substring.Raw) : ∀ n, s.prevn n 0 = 0
  | 0 => rfl
  | n+1 => by simp [prevn, prevn_zero s n]

end Substring.Raw

section Deprecations

@[deprecated Substring.Raw (since := "2025-11-16")]
abbrev Substring := Substring.Raw

@[deprecated Substring.Raw.bsize (since := "2025-11-16")]
abbrev Substring.bsize := Substring.Raw.bsize

@[deprecated Substring.Raw.toString (since := "2025-11-16")]
abbrev Substring.toString := Substring.Raw.toString

@[deprecated Substring.Raw.isEmpty (since := "2025-11-16")]
abbrev Substring.isEmpty := Substring.Raw.isEmpty

@[deprecated Substring.Raw.next (since := "2025-11-16")]
abbrev Substring.next := Substring.Raw.next

@[deprecated Substring.Raw.prev (since := "2025-11-16")]
abbrev Substring.prev := Substring.Raw.prev

@[deprecated Substring.Raw.atEnd (since := "2025-11-16")]
abbrev Substring.atEnd := Substring.Raw.atEnd

@[deprecated Substring.Raw.beq (since := "2025-11-16")]
abbrev Substring.beq := Substring.Raw.beq

end Deprecations
