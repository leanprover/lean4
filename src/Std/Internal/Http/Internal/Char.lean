/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Init.Data.String

public section

/-!
# HTTP Character Predicates

This module provides shared character validation predicates used across the HTTP library.
It includes both token-character validation for HTTP headers (RFC 9110 §5.6.2) and
URI character classification (RFC 3986).
-/

namespace Std.Http.Internal.Char

set_option linter.all true

/--
Checks if a character is a valid HTTP token character per RFC 9110 §5.6.2.
Token characters include alphanumerics and the following: `` !#$%&'*+-.^_`|~ ``

The bitmask `0x57ffffffc7fffffe03ff6cfa00000000` encodes exactly the 128-bit set of
allowed ASCII token characters: bit `i` is set iff ASCII code point `i` is a token
character. `Nat.testBit` then performs an O(1) membership test.
-/
@[expose]
def isTokenCharacter (c : Char) : Bool :=
  c.toNat < 128 && Nat.testBit 0x57ffffffc7fffffe03ff6cfa00000000 c.toNat

/--
Checks if a byte represents an ASCII character (value < 128).
-/
@[expose]
def isAscii (c : UInt8) : Bool :=
  c < 128

/--
Checks if a byte is a decimal digit (0-9).
-/
@[inline, expose]
def isDigit (c : UInt8) : Bool :=
  c >= '0'.toUInt8 ∧ c <= '9'.toUInt8

/--
Checks if a byte is an alphabetic character (a-z or A-Z).
-/
@[inline, expose]
def isAlpha (c : UInt8) : Bool :=
  (c >= 'A'.toUInt8 ∧ c <= 'Z'.toUInt8) ∨ (c >= 'a'.toUInt8 ∧ c <= 'z'.toUInt8)

/--
Checks if a byte is a hexadecimal digit (0-9, a-f, or A-F). Note: This accepts both lowercase and
uppercase hex digits.
-/
@[expose]
def isHexDigit (c : UInt8) : Bool :=
  (c ≥ '0'.toUInt8 && c ≤ '9'.toUInt8) ||
  (c ≥ 'a'.toUInt8 && c ≤ 'f'.toUInt8) ||
  (c ≥ 'A'.toUInt8 && c ≤ 'F'.toUInt8)

/--
Checks if a byte is an alphanumeric digit (0-9, a-z, or A-Z).
-/
@[expose]
def isAlphaNum (c : UInt8) : Bool :=
  (c ≥ '0'.toUInt8 && c ≤ '9'.toUInt8) ||
  (c ≥ 'a'.toUInt8 && c ≤ 'z'.toUInt8) ||
  (c ≥ 'A'.toUInt8 && c ≤ 'Z'.toUInt8)

/--
Checks if a byte is an unreserved character according to RFC 3986. Unreserved characters are:
alphanumeric, hyphen, period, underscore, and tilde.
-/
@[expose]
def isUnreserved (c : UInt8) : Bool :=
  isAlphaNum c ||
  (c = '-'.toUInt8 || c = '.'.toUInt8 || c = '_'.toUInt8 || c = '~'.toUInt8)

/--
Checks if a byte is a sub-delimiter character according to RFC 3986.
Sub-delimiters are: `!`, `$`, `&`, `'`, `(`, `)`, `*`, `+`, `,`, `;`, `=`.
-/
@[expose]
def isSubDelims (c : UInt8) : Bool :=
  c = '!'.toUInt8 || c = '$'.toUInt8 || c = '&'.toUInt8 || c = '\''.toUInt8 ||
  c = '('.toUInt8 || c = ')'.toUInt8 || c = '*'.toUInt8 || c = '+'.toUInt8 ||
  c = ','.toUInt8 || c = ';'.toUInt8 || c = '='.toUInt8

/--
Checks if a byte is a valid path character (`pchar`) according to RFC 3986.
`pchar = unreserved / pct-encoded / sub-delims / ":" / "@"`

Note: The percent-encoding (`pct-encoded`) is handled separately by `isEncodedChar`,
so this predicate only covers the non-percent characters.
-/
@[expose]
def isPChar (c : UInt8) : Bool :=
  isUnreserved c || isSubDelims c || c = ':'.toUInt8 || c = '@'.toUInt8

/--
Checks if a byte is a valid character in a URI query component according to RFC 3986.
`query = *( pchar / "/" / "?" )`
-/
@[expose]
def isQueryChar (c : UInt8) : Bool :=
  isPChar c || c = '/'.toUInt8 || c = '?'.toUInt8

/--
Checks if a byte is a valid character in a URI fragment component according to RFC 3986.
`fragment = *( pchar / "/" / "?" )`
-/
@[expose]
def isFragmentChar (c : UInt8) : Bool :=
  isPChar c || c = '/'.toUInt8 || c = '?'.toUInt8

/--
Checks if a byte is a valid character in a URI userinfo component according to RFC 3986.
`userinfo = *( unreserved / pct-encoded / sub-delims / ":" )`
-/
@[expose]
def isUserInfoChar (c : UInt8) : Bool :=
  isUnreserved c || isSubDelims c || c = ':'.toUInt8

end Std.Http.Internal.Char
