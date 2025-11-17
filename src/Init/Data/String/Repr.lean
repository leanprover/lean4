/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Mario Carneiro
-/
module

prelude
public import Init.Data.String.Substring

public section

/--
Interprets a string as the decimal representation of an integer, returning it. Returns `none` if
the string does not contain a decimal integer.

A string can be interpreted as a decimal integer if it only consists of at least one decimal digit
and optionally `-` in front. Leading `+` characters are not allowed.

Use `String.isInt` to check whether `String.toInt?` would return `some`. `String.toInt!` is an
alternative that panics instead of returning `none` when the string is not an integer.

Examples:
 * `"".toInt? = none`
 * `"-".toInt? = none`
 * `"0".toInt? = some 0`
 * `"5".toInt? = some 5`
 * `"-5".toInt? = some (-5)`
 * `"587".toInt? = some 587`
 * `"-587".toInt? = some (-587)`
 * `" 5".toInt? = none`
 * `"2-3".toInt? = none`
 * `"0xff".toInt? = none`
-/
def String.toInt? (s : String) : Option Int := do
  if s.front = '-' then do
    let v ← (s.toRawSubstring.drop 1).toNat?;
    pure <| - Int.ofNat v
  else
   Int.ofNat <$> s.toNat?

/--
Checks whether the string can be interpreted as the decimal representation of an integer.

A string can be interpreted as a decimal integer if it only consists of at least one decimal digit
and optionally `-` in front. Leading `+` characters are not allowed.

Use `String.toInt?` or `String.toInt!` to convert such a string to an integer.

Examples:
 * `"".isInt = false`
 * `"-".isInt = false`
 * `"0".isInt = true`
 * `"-0".isInt = true`
 * `"5".isInt = true`
 * `"587".isInt = true`
 * `"-587".isInt = true`
 * `"+587".isInt = false`
 * `" 5".isInt = false`
 * `"2-3".isInt = false`
 * `"0xff".isInt = false`
-/
def String.isInt (s : String) : Bool :=
  if s.front = '-' then
    (s.toRawSubstring.drop 1).isNat
  else
    s.isNat

/--
Interprets a string as the decimal representation of an integer, returning it. Panics if the string
does not contain a decimal integer.

A string can be interpreted as a decimal integer if it only consists of at least one decimal digit
and optionally `-` in front. Leading `+` characters are not allowed.

Use `String.isInt` to check whether `String.toInt!` would return a value. `String.toInt?` is a safer
alternative that returns `none` instead of panicking when the string is not an integer.

Examples:
 * `"0".toInt! = 0`
 * `"5".toInt! = 5`
 * `"587".toInt! = 587`
 * `"-587".toInt! = -587`
-/
def String.toInt! (s : String) : Int :=
  match s.toInt? with
  | some v => v
  | none   => panic "Int expected"
