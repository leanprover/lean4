/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving, Markus Himmel
-/
module

prelude
public import Init.Data.String.Basic
import Init.Data.String.Iterate
import Init.Data.String.Slice.Pattern

set_option doc.verso true

public section

namespace String.Slice

/--
Checks whether the slice can be interpreted as the decimal representation of a natural number.

A slice can be interpreted as a decimal natural number if it is not empty and all the characters in
it are digits. Underscores ({lit}`_`) are allowed as digit separators for readability, but cannot appear
at the start, at the end, or consecutively.

Use {name (scope := "Init.Data.String.Slice.Numeric")}`toNat?` or
{name (scope := "Init.Data.String.Slice.Numeric")}`toNat!` to convert such a slice to a natural number.

Examples:
 * {lean}`"".toSlice.isNat = false`
 * {lean}`"0".toSlice.isNat = true`
 * {lean}`"5".toSlice.isNat = true`
 * {lean}`"05".toSlice.isNat = true`
 * {lean}`"587".toSlice.isNat = true`
 * {lean}`"1_000".toSlice.isNat = true`
 * {lean}`"100_000_000".toSlice.isNat = true`
 * {lean}`"-587".toSlice.isNat = false`
 * {lean}`" 5".toSlice.isNat = false`
 * {lean}`"2+3".toSlice.isNat = false`
 * {lean}`"0xff".toSlice.isNat = false`
 * {lean}`"_123".toSlice.isNat = false`
 * {lean}`"123_".toSlice.isNat = false`
 * {lean}`"12__34".toSlice.isNat = false`
-/
def isNat (s : Slice) : Bool := Id.run do
  let mut lastWasDigit := false

  for c in s do
    if c = '_' then
      if !lastWasDigit then
        return false
      lastWasDigit := false
    else if c.isDigit then
      lastWasDigit := true
    else
      return false

  return lastWasDigit

/--
Interprets a slice as the decimal representation of a natural number, returning it. Returns
{name}`none` if the slice does not contain a decimal natural number.

A slice can be interpreted as a decimal natural number if it is not empty and all the characters in
it are digits. Underscores ({lit}`_`) are allowed as digit separators and are ignored during parsing.

Use {name}`isNat` to check whether {name}`toNat?` would return {name}`some`.
{name (scope := "Init.Data.String.Slice.Numeric")}`toNat!` is an alternative that panics instead of
returning {name}`none` when the slice is not a natural number.

Examples:
 * {lean}`"".toSlice.toNat? = none`
 * {lean}`"0".toSlice.toNat? = some 0`
 * {lean}`"5".toSlice.toNat? = some 5`
 * {lean}`"587".toSlice.toNat? = some 587`
 * {lean}`"1_000".toSlice.toNat? = some 1000`
 * {lean}`"100_000_000".toSlice.toNat? = some 100000000`
 * {lean}`"-587".toSlice.toNat? = none`
 * {lean}`" 5".toSlice.toNat? = none`
 * {lean}`"2+3".toSlice.toNat? = none`
 * {lean}`"0xff".toSlice.toNat? = none`
-/
def toNat? (s : Slice) : Option Nat :=
  if s.isNat then
    some <| s.foldl (fun n c => if c = '_' then n else n * 10 + (c.toNat - '0'.toNat)) 0
  else
    none

/--
Interprets a slice as the decimal representation of a natural number, returning it. Panics if the
slice does not contain a decimal natural number.

A slice can be interpreted as a decimal natural number if it is not empty and all the characters in
it are digits. Underscores ({lit}`_`) are allowed as digit separators and are ignored during parsing.

Use {name}`isNat` to check whether {name}`toNat!` would return a value. {name}`toNat?` is a safer
alternative that returns {name}`none` instead of panicking when the string is not a natural number.

Examples:
 * {lean}`"0".toSlice.toNat! = 0`
 * {lean}`"5".toSlice.toNat! = 5`
 * {lean}`"587".toSlice.toNat! = 587`
 * {lean}`"1_000".toSlice.toNat! = 1000`
-/
def toNat! (s : Slice) : Nat :=
  if s.isNat then
    s.foldl (fun n c => if c = '_' then n else n * 10 + (c.toNat - '0'.toNat)) 0
  else
    panic! "Nat expected"

/--
Checks whether the slice can be interpreted as the decimal representation of an integer.

A slice can be interpreted as a decimal integer if it only consists of at least one decimal digit
and optionally {lit}`-` in front. Leading {lit}`+` characters are not allowed.

Use {name (scope := "Init.Data.String.Slice.Numeric")}`String.Slice.toInt?` or {name (scope := "Init.Data.String.Slice.Numeric")}`String.Slice.toInt!` to convert such a string to an integer.

Examples:
 * {lean}`"".toSlice.isInt = false`
 * {lean}`"-".toSlice.isInt = false`
 * {lean}`"0".toSlice.isInt = true`
 * {lean}`"-0".toSlice.isInt = true`
 * {lean}`"5".toSlice.isInt = true`
 * {lean}`"587".toSlice.isInt = true`
 * {lean}`"-587".toSlice.isInt = true`
 * {lean}`"+587".toSlice.isInt = false`
 * {lean}`" 5".toSlice.isInt = false`
 * {lean}`"2-3".toSlice.isInt = false`
 * {lean}`"0xff".toSlice.isInt = false`
 * {lean}`"-0_1".toSlice.isInt = true`
 * {lean}`"-_1".toSlice.isInt = false`
-/
def isInt (s : Slice) : Bool :=
  match s.dropPrefix? '-' with
  | some rest => rest.isNat
  | none => s.isNat

/--
Interprets a slice as the decimal representation of an integer, returning it. Returns {lean}`none` if
the string does not contain a decimal integer.

A string can be interpreted as a decimal integer if it only consists of at least one decimal digit
and optionally {lit}`-` in front. Leading {lit}`+` characters are not allowed.

Use {name}`Slice.isInt` to check whether {name}`Slice.toInt?` would return {lean}`some`.
{name (scope := "Init.Data.String.Slice.Numeric")}`Slice.toInt!` is an alternative that panics instead of
returning {lean}`none` when the string is not an integer.

Examples:
 * {lean}`"".toSlice.toInt? = none`
 * {lean}`"-".toSlice.toInt? = none`
 * {lean}`"0".toSlice.toInt? = some 0`
 * {lean}`"5".toSlice.toInt? = some 5`
 * {lean}`"-5".toSlice.toInt? = some (-5)`
 * {lean}`"587".toSlice.toInt? = some 587`
 * {lean}`"-587".toSlice.toInt? = some (-587)`
 * {lean}`" 5".toSlice.toInt? = none`
 * {lean}`"2-3".toSlice.toInt? = none`
 * {lean}`"0xff".toSlice.toInt? = none`
 * {lean}`"-0_1".toSlice.toInt? = some (-1)`
 * {lean}`"-_1".toSlice.toInt? = none`
-/
def toInt? (s : Slice) : Option Int :=
  match s.dropPrefix? '-' with
  | some rest => rest.toNat?.map Int.negOfNat
  | none => s.toNat?.map Int.ofNat

/--
Interprets a string as the decimal representation of an integer, returning it. Panics if the string
does not contain a decimal integer.

A string can be interpreted as a decimal integer if it only consists of at least one decimal digit
and optionally {lit}`-` in front. Leading `+` characters are not allowed.

Use {name}`Slice.isInt` to check whether {name}`Slice.toInt!` would return a value.
{name}`Slice.toInt?` is a safer alternative that returns {lean}`none` instead of panicking when the
string is not an integer.

Examples:
 * {lean}`"0".toSlice.toInt! = 0`
 * {lean}`"5".toSlice.toInt! = 5`
 * {lean}`"587".toSlice.toInt! = 587`
 * {lean}`"-587".toSlice.toInt! = -587`
-/
@[inline]
def toInt! (s : Slice) : Int :=
  match s.toInt? with
  | some v => v
  | none   => panic "Int expected"

end String.Slice
