/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Init.Data.Char
public import Init.Data.String.Basic
public import Init.Data.Int
public import Init.Grind

@[expose]
public section

/-!
# HTTP Character Predicates

This module provides shared character validation predicates used across the HTTP library.
All predicates in this module are ASCII-only by design (`isAscii c` where applicable), and
intentionally exclude `obs-text` and all non-ASCII code points.
-/

namespace Std.Http.Internal.Char

set_option linter.all true

/--
Checks if a character is ASCII (Unicode code point < 128).
-/
@[inline, expose]
def isAscii (c : Char) : Bool :=
  c.toNat < 128

/--
Checks if a byte represents an ASCII character (value < 128).
-/
@[inline, expose]
def isAsciiByte (c : UInt8) : Bool :=
  c < 128

/--
Checks if a byte is a decimal digit (0-9).
-/
@[inline, expose]
def isDigitByte (c : UInt8) : Bool :=
  c >= '0'.toUInt8 && c <= '9'.toUInt8

/--
Checks if a byte is an alphabetic character (a-z or A-Z).
-/
@[inline, expose]
def isAlphaByte (c : UInt8) : Bool :=
  (c >= 'A'.toUInt8 && c <= 'Z'.toUInt8) || (c >= 'a'.toUInt8 && c <= 'z'.toUInt8)

/--
tchar = "!" / "#" / "$" / "%" / "&" / "'" / "*"
  / "+" / "-" / "." / "^" / "_" / "`" / "|" / "~"
  / DIGIT / ALPHA
  ; Visible token characters used to build `token`.
-/
@[inline]
def tchar (c : Char) : Bool :=
  (c matches '!' | '#' | '$' | '%' | '&' | '\'' | '*' | '+' | '-' | '.' | '^' | '_' | '`' | '|' | '~') ||
  Char.isDigit c ||
  Char.isAlpha c

/--
vchar = %x21-7E
; Visible (printing) ASCII characters.
-/
@[inline]
def vchar (c : Char) : Bool :=
  c ≥ '!' ∧ c ≤ '~'

/--
qdtext = HTAB / SP / %x21 / %x23-5B / %x5D-7E
; ASCII-only variant (no obs-text).
-/
@[inline]
def qdtext (c : Char) : Bool :=
  (c matches '\t' | ' ' | '!') ||
  ('#' ≤ c ∧ c ≤ '[') ||
  (']' ≤ c ∧ c ≤ '~')

/--
quoted-pair = "\\" ( HTAB / SP / VCHAR )
; ASCII-only variant (no obs-text).
-/
@[inline]
def quotedPairChar (c : Char) : Bool :=
  (c matches '\t' | ' ') || vchar c

/--
quoted-string body character class:
( qdtext / quoted-pair payload ) in ASCII-only mode.
-/
@[inline]
def quotedStringChar (c : Char) : Bool :=
  qdtext c || quotedPairChar c

theorem quotedStringChar_lt_0x80 : quotedStringChar c → c < '\x80' := by
  simp [quotedStringChar, qdtext, quotedPairChar]
  split <;> simp only [true_or, Char.reduceLT, imp_self]
  grind [→ Char.le_def.mp, Char.lt_def.mpr, vchar]

private theorem not_quotedStringChar_ofNat_aux :
    ∀ c : Nat, c < 128 → ¬(qdtext (Char.ofNat c)) ∧ ¬((Char.ofNat c = '\"') ∨ (Char.ofNat c = '\\')) →
    ¬(quotedStringChar (Char.ofNat c)) := by
  decide

theorem not_quotedStringChar_of_not_qdtext_not_dquote_backslash :
    ∀ c : Char, c < '\x80' → ¬(qdtext (c)) ∧ ¬((c = '\"') || (c = '\\')) →
    ¬(quotedStringChar c) := by
  intro c hlt hq
  simpa [Char.ofNat_toNat] using
    (not_quotedStringChar_ofNat_aux
      c.toNat hlt (by simpa [Char.ofNat_toNat] using hq))

/--
field-vchar = VCHAR
; ASCII-only variant (no obs-text).
-/
@[inline]
def fieldVchar (c : Char) : Bool :=
  vchar c

/--
field-content character class:
field-vchar / SP / HTAB
; ASCII-only variant (no obs-text).
-/
@[inline]
def fieldContent (c : Char) : Bool :=
  fieldVchar c || (c matches ' ' | '\t')

/--
ctext = HTAB / SP / %x21-27 / %x2A-5B / %x5D-7E
; ASCII-only variant (no obs-text).
-/
@[inline]
def ctext (c : Char) : Bool :=
  (c matches '\t' | ' ') ||
  ('!' ≤ c ∧ c ≤ '\'') ||
  ('*' ≤ c ∧ c ≤ '[') ||
  (']' ≤ c ∧ c ≤ '~')

/--
etagc = "!" / %x23-7E
; ASCII-only variant (no obs-text).
-/
@[inline]
def etagc (c : Char) : Bool :=
  c = '!' || ('#' ≤ c ∧ c ≤ '~')

/--
OWS = *( SP / HTAB )  (character class only)
-/
@[inline]
def ows (c : Char) : Bool :=
  c matches ' ' | '\t'

/--
BWS = OWS (character class alias)
-/
@[inline]
def bws (c : Char) : Bool :=
  ows c

/--
RWS = 1*( SP / HTAB ) (character class is identical to `ows`)
-/
@[inline]
def rws (c : Char) : Bool :=
  ows c

/--
obs-text = %x80-FF (and higher Unicode scalar values in this library's `Char` model).
-/
@[inline]
def obsText (c : Char) : Bool :=
  0x80 ≤ c.toNat

/--
reason-phrase character class:
HTAB / SP / VCHAR
; ASCII-only variant (no obs-text).

Reference: https://httpwg.org/specs/rfc9110.html#reason.phrase
-/
@[inline]
def reasonPhraseChar (c : Char) : Bool :=
  (c matches '\t' | ' ') || vchar c

/--
Checks if a character is a hexadecimal digit (0-9, a-f, or A-F).
-/
@[inline, expose]
def isHexDigit (c : Char) : Bool :=
  (c matches 'a' | 'b' | 'c' | 'd' | 'e' | 'f' | 'A' | 'B' | 'C' | 'D' | 'E' | 'F') ||
  Char.isDigit c

/--
Checks if a byte is a hexadecimal digit (0-9, a-f, or A-F).
-/
@[inline, expose]
def isHexDigitByte (c : UInt8) : Bool :=
  (c ≥ '0'.toUInt8 && c ≤ '9'.toUInt8) ||
  (c ≥ 'a'.toUInt8 && c ≤ 'f'.toUInt8) ||
  (c ≥ 'A'.toUInt8 && c ≤ 'F'.toUInt8)

/--
Checks if a byte is an alphanumeric digit (0-9, a-z, or A-Z).
-/
@[inline, expose]
def isAlphaNum (c : UInt8) : Bool :=
  (c ≥ '0'.toUInt8 && c ≤ '9'.toUInt8) ||
  (c ≥ 'a'.toUInt8 && c ≤ 'z'.toUInt8) ||
  (c ≥ 'A'.toUInt8 && c ≤ 'Z'.toUInt8)

/--
Checks whether `c` is an ASCII alphanumeric character.
-/
@[inline, expose]
def isAsciiAlphaNumChar (c : Char) : Bool :=
  isAscii c && (Char.isDigit c || Char.isAlpha c)

/--
Checks if a character is valid after the first character of a URI scheme.
Valid characters are ASCII alphanumeric, `+`, `-`, and `.`.
-/
@[inline, expose]
def isValidSchemeChar (c : Char) : Bool :=
  isAsciiAlphaNumChar c || (c matches '+' | '-' | '.')

/--
Checks if a character is valid for use in a domain name.
Valid characters are ASCII alphanumeric, hyphens, and dots.
-/
@[inline, expose]
def isValidDomainNameChar (c : Char) : Bool :=
  isAsciiAlphaNumChar c || (c matches '-' | '.')

/--
Checks if a byte is an unreserved character according to RFC 3986. Unreserved characters are:
alphanumeric, hyphen, period, underscore, and tilde.
-/
@[inline, expose]
def isUnreserved (c : UInt8) : Bool :=
  isAlphaNum c ||
  (c = '-'.toUInt8 || c = '.'.toUInt8 || c = '_'.toUInt8 || c = '~'.toUInt8)

/--
Checks if a byte is a sub-delimiter character according to RFC 3986.
Sub-delimiters are: `!`, `$`, `&`, `'`, `(`, `)`, `*`, `+`, `,`, `;`, `=`.
-/
@[inline, expose]
def isSubDelims (c : UInt8) : Bool :=
  c = '!'.toUInt8 || c = '$'.toUInt8 || c = '&'.toUInt8 || c = ('\'' : Char).toUInt8 ||
  c = '('.toUInt8 || c = ')'.toUInt8 || c = '*'.toUInt8 || c = '+'.toUInt8 ||
  c = ','.toUInt8 || c = ';'.toUInt8 || c = '='.toUInt8

/--
Checks if a byte is a valid path character (`pchar`) according to RFC 3986.
`pchar = unreserved / pct-encoded / sub-delims / ":" / "@"`

Note: The percent-encoding (`pct-encoded`) is handled separately by `isEncodedChar`,
so this predicate only covers the non-percent characters.
-/
@[inline, expose]
def isPChar (c : UInt8) : Bool :=
  isUnreserved c || isSubDelims c || c = ':'.toUInt8 || c = '@'.toUInt8

/--
Checks if a byte is a valid character in a URI query component according to RFC 3986.
`query = *( pchar / "/" / "?" )`
-/
@[inline, expose]
def isQueryChar (c : UInt8) : Bool :=
  isPChar c || c = '/'.toUInt8 || c = '?'.toUInt8

/--
Checks if a byte is a valid character in a URI fragment component according to RFC 3986.
`fragment = *( pchar / "/" / "?" )`
-/
@[inline, expose]
def isFragmentChar (c : UInt8) : Bool :=
  isPChar c || c = '/'.toUInt8 || c = '?'.toUInt8

/--
Checks if a byte is a valid character in a URI userinfo component according to RFC 3986.
`userinfo = *( unreserved/ sub-delims / ":" )`

Note: It avoids the pct-encoded of the original grammar because it is used with `Encoding.lean`
that provides it.
-/
@[inline, expose]
def isUserInfoChar (c : UInt8) : Bool :=
  isUnreserved c || isSubDelims c || c = ':'.toUInt8

/--
Checks if a byte is a valid character in a URI query component,
excluding the typical key/value separators `&` and `=`.

Inspired by `query = *( pchar / "/" / "?" )` from RFC 3986,
but disallows `&` and `=` so they can be treated as structural separators.
-/
@[inline, expose]
def isQueryDataChar (c : UInt8) : Bool :=
  isQueryChar c && c ≠ '&'.toUInt8 && c ≠ '='.toUInt8

end Std.Http.Internal.Char
