/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving, Markus Himmel
-/
module

prelude
public import Init.Data.String.Basic
public import Init.Data.String.FindPos
public import Init.Data.String.Compare
public import Init.Data.Ord.Basic
import Init.Data.String.Pattern.Memcmp
import Init.Omega

set_option doc.verso true

public section

namespace String.Slice

instance : HAppend String String.Slice String where
  -- This implementation performs an unnecessary copy which could be avoided by providing a custom
  -- C++ implementation for this instance. Note: if `String` had no custom runtime representation
  -- at all, then this would be very easy to get right from Lean using `ByteArray.copySlice`.
  hAppend s t := s ++ t.copy

/--
Checks whether {name}`s1` and {name}`s2` represent the same string, even if they are slices of
different base strings or different slices within the same string.

The implementation is an efficient equivalent of {lean}`s1.copy == s2.copy`
-/
def beq (s1 s2 : Slice) : Bool :=
  if h : s1.utf8ByteSize = s2.utf8ByteSize then
    have h1 := by simp [String.Pos.Raw.le_iff]
    have h2 := by simp [h, String.Pos.Raw.le_iff]
    Pattern.Internal.memcmpSlice s1 s2 s1.startPos.offset s2.startPos.offset s1.utf8ByteSize h1 h2
  else
    false

instance : BEq Slice where
  beq := beq

@[inherit_doc Slice.copy]
def toString (s : Slice) : String :=
  s.copy

@[simp]
theorem toString_eq : toString = copy := (rfl)

instance : ToString String.Slice where
  toString := toString

@[simp]
theorem toStringToString_eq : ToString.toString = String.Slice.copy := (rfl)

@[extern "lean_slice_hash"]
protected def hash (s : @& Slice) : UInt64 :=
  String.hash s.copy

instance : Hashable Slice where
  hash := Slice.hash

/--
Checks whether {name}`s` is lexicographically smaller than {name}`t`.

The implementation is an efficient equivalent of {lean}`decide (s.copy < t.copy)`.
-/
def blt (s t : Slice) : Bool :=
  if h : s.utf8ByteSize < t.utf8ByteSize then
    -- `s` is shorter, so it is smaller unless the first `s.utf8ByteSize` bytes of `t` are smaller.
    have h1 := by simp [Pos.Raw.le_iff]; omega
    have h2 := by simp [Pos.Raw.le_iff]
    !Pattern.Internal.memcmpSliceLt t s t.startPos.offset s.startPos.offset s.utf8ByteSize h1 h2
  else
    have h1 := by simp [Pos.Raw.le_iff]; omega
    have h2 := by simp [Pos.Raw.le_iff]
    Pattern.Internal.memcmpSliceLt s t s.startPos.offset t.startPos.offset t.utf8ByteSize h1 h2

instance : LT Slice where
  lt x y := x.blt y = true

instance : DecidableLT Slice :=
  fun x y => inferInstanceAs (Decidable (x.blt y = true))

/--
Compares {name}`s` and {name}`t` lexicographically.

The implementation is an efficient equivalent of {lean}`compare s.copy t.copy`.
-/
protected def compare (s t : Slice) : Ordering :=
  have h1 := by simp [Pos.Raw.le_iff]; omega
  have h2 := by simp [Pos.Raw.le_iff]; omega
  (Pattern.Internal.memcmpSliceCompare s t s.startPos.offset t.startPos.offset
    (min s.utf8ByteSize t.utf8ByteSize) h1 h2).then (Ord.compare s.utf8ByteSize t.utf8ByteSize)

instance : Ord Slice where
  compare := Slice.compare

instance : LE Slice where
  le x y := ¬y < x

instance : DecidableLE Slice :=
  fun x y => inferInstanceAs (Decidable (¬y < x))

instance : Min Slice := .leftLeaningOfLE _
instance : Max Slice := .leftLeaningOfLE _

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

/--
Appends all the slices in a list of slices, in order.

Use {name}`String.Slice.intercalate` to place a separator string between the strings in a list.

Examples:
 * {lean}`String.Slice.join ["gr", "ee", "n"] = "green"`
 * {lean}`String.Slice.join ["b", "", "l", "", "ue"] = "blue"`
 * {lean}`String.Slice.join [] = ""`
-/
def join (l : List String.Slice) : String :=
  l.foldl (fun (r : String) (s : String.Slice) => r ++ s) ""

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
