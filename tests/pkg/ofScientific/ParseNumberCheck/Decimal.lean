/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julia M. Himmel
-/
module

/-!
Helpers shared by `ParseNumberCheck`, which checks the `OfScientific Float` and
`OfScientific Float32` instances (the decimal-to-float conversion behind float
literals) against test vectors in the `parse-number-fxx-test-data` format.

The central piece is `parseDecimal`, which turns a decimal string such as
`-1.23e-5` into a `Decimal` (an exact `mantissa * 10 ^ exponent`, plus a sign)
and `Decimal.toFloat`/`Decimal.toFloat32`, which feed that decomposition through
`OfScientific.ofScientific` exactly as the elaborator does for a float literal.
-/

/--
A decimal number `(if negative then -1 else 1) * mantissa * 10 ^ exponent`,
the decomposition the `OfScientific` instances consume. `mantissa` collects every
significant digit (integer and fractional) as one natural number; `exponent` folds
in both the position of the decimal point and any explicit `e` exponent.
-/
public structure Decimal where
  /-- Whether a leading `-` was present (carried separately since `OfScientific` has no sign). -/
  negative : Bool
  /-- All significant digits, integer and fractional, as a single natural number. -/
  mantissa : Nat
  /-- The power of ten the mantissa is scaled by. -/
  exponent : Int
deriving Repr, DecidableEq, Inhabited

/-- The leading run of decimal digits of `cs`, paired with the remaining characters. -/
private def takeDigits : List Char → List Char × List Char
  | [] => ([], [])
  | c :: cs =>
    if c.isDigit then
      let (ds, rest) := takeDigits cs
      (c :: ds, rest)
    else
      ([], c :: cs)

/-- Interpret a list of decimal-digit characters as a natural number (empty is `0`). -/
private def digitsToNat (ds : List Char) : Nat :=
  ds.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0

/--
Parse the exponent following an `e`/`E`: an optional sign and at least one digit.
Returns the signed exponent together with any trailing characters (which the
caller requires to be empty).
-/
private def parseExp (cs : List Char) : Option (Int × List Char) :=
  let (esign, cs) :=
    match cs with
    | '-' :: rest => (true, rest)
    | '+' :: rest => (false, rest)
    | _ => (false, cs)
  let (digits, rest) := takeDigits cs
  if digits.isEmpty then none
  else
    let n : Int := digitsToNat digits
    some (if esign then -n else n, rest)

/--
Parse a decimal floating-point string in the form accepted by the
`parse-number-fxx-test-data` vectors (and by C's `strtod`): an optional sign, an
integer part, an optional fractional part after a `.`, and an optional `e`/`E`
exponent. Either the integer or the fractional part may be empty (e.g. `.5` or
`5.`), but at least one digit must be present overall. Returns `none` for input
the parser does not recognize, including any trailing garbage.
-/
public def parseDecimal (s : String) : Option Decimal := do
  let cs := s.toList
  let (negative, cs) :=
    match cs with
    | '-' :: rest => (true, rest)
    | '+' :: rest => (false, rest)
    | _ => (false, cs)
  let (intDigits, cs) := takeDigits cs
  let (fracDigits, cs) :=
    match cs with
    | '.' :: rest => takeDigits rest
    | _ => ([], cs)
  guard !(intDigits.isEmpty && fracDigits.isEmpty)
  let (expVal, cs) ←
    match cs with
    | 'e' :: rest | 'E' :: rest => parseExp rest
    | _ => some (0, cs)
  guard cs.isEmpty
  return {
    negative
    mantissa := digitsToNat (intDigits ++ fracDigits)
    -- Each fractional digit shifts the implied decimal point one place right.
    exponent := expVal - fracDigits.length
  }

/--
The magnitude `mantissa * 10 ^ exponent` as the `OfScientific Float` instance
computes it. `OfScientific.ofScientific` takes the exponent as a sign flag plus a
natural number, so a negative `exponent` becomes `(true, -exponent)`.
-/
private def Decimal.magnitude (d : Decimal) : Float :=
  if d.exponent ≥ 0 then
    OfScientific.ofScientific d.mantissa false d.exponent.toNat
  else
    OfScientific.ofScientific d.mantissa true (-d.exponent).toNat

/-- `binary32` counterpart of `Decimal.magnitude`, driving the `OfScientific Float32` instance. -/
private def Decimal.magnitude32 (d : Decimal) : Float32 :=
  if d.exponent ≥ 0 then
    OfScientific.ofScientific d.mantissa false d.exponent.toNat
  else
    OfScientific.ofScientific d.mantissa true (-d.exponent).toNat

/-- Convert to `Float` exactly as a float literal would, including the sign. -/
public def Decimal.toFloat (d : Decimal) : Float :=
  if d.negative then -d.magnitude else d.magnitude

/-- Convert to `Float32` exactly as a `Float32` literal would, including the sign. -/
public def Decimal.toFloat32 (d : Decimal) : Float32 :=
  if d.negative then -d.magnitude32 else d.magnitude32
