/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Internal.Parsec
import Std.Time.Date
import Std.Time.Time
import Std.Time.Zoned
import Std.Time.DateTime

/-!
This module defines the `Formatter` types. It is based on the Java's `DateTimeFormatter` format.
-/

namespace Std
namespace Time
open Internal
open Std.Internal.Parsec.String
open Std.Internal.Parsec Lean PlainTime PlainDate TimeZone DateTime

set_option linter.all true


/--
`Text` represents different text formatting styles.
-/
inductive Text
  /-- Short form (e.g., "Tue") -/
  | short
  /-- Full form (e.g., "Tuesday") -/
  | full
  /-- Narrow form (e.g., "T") -/
  | narrow
  deriving Repr, Inhabited

namespace Text

/--
`classify` classifies the number of pattern letters into a `Text` type.
-/
def classify (num : Nat) : Option Text :=
  if num < 4 then
    some (.short)
  else if num = 4 then
    some (.full)
  else if num = 5 then
    some (.narrow)
  else
    none

end Text

/--
`Number` represents different number formatting styles.
-/
structure Number where
  /--
  The number of digits to pad, based on the count of pattern letters.
  -/
  padding : Nat
  deriving Repr, Inhabited

/--
`classifyNumberText` classifies the number of pattern letters into either a `Number` or `Text`.
-/
def classifyNumberText : Nat → Option (Number ⊕ Text)
  | n => if n < 3 then some (.inl ⟨n⟩) else .inr <$> (Text.classify n)

/--
`Fraction` represents the fraction of a second, which can either be full nanoseconds
or a truncated form with fewer digits.
-/
inductive Fraction
  /-- Nanosecond precision (up to 9 digits) -/
  | nano
  /-- Fewer digits (truncated precision) -/
  | truncated (digits : Nat)
  deriving Repr, Inhabited

namespace Fraction

/--
`classify` classifies the number of pattern letters into either a `Fraction`. It's used for `nano`.
-/
def classify (nat : Nat) : Option Fraction :=
  if nat < 9 then
    some (.truncated nat)
  else if nat = 9 then
    some (.nano)
  else
    none

end Fraction

/--
`Year` represents different year formatting styles based on the number of pattern letters.
-/
inductive Year
  /-- Any size (e.g., "19000000000000") -/
  | any
  /-- Two-digit year format (e.g., "23" for 2023) -/
  | twoDigit
  /-- Four-digit year format (e.g., "2023") -/
  | fourDigit
  /-- Extended year format for more than 4 digits (e.g., "002023") -/
  | extended (num : Nat)
  deriving Repr, Inhabited

namespace Year

/--
`classify` classifies the number of pattern letters into a `Year` format.
-/
def classify (num : Nat) : Option Year :=
  if num = 1 then
    some .any
  else if num = 2 then
    some .twoDigit
  else if num = 4 then
    some .fourDigit
  else if num > 4 ∨ num = 3 then
    some (.extended num)
  else
    none

end Year

/--
`ZoneId` represents different time zone ID formats based on the number of pattern letters.
-/
inductive ZoneId
  /-- Short form of time zone (e.g., "PST") -/
  | short
  /-- Full form of time zone (e.g., "Pacific Standard Time") -/
  | full
  deriving Repr, Inhabited

namespace ZoneId

/--
`classify` classifies the number of pattern letters into a `ZoneId` format.
- If 2 letters, it returns the short form.
- If 4 letters, it returns the full form.
- Otherwise, it returns none.
-/
def classify (num : Nat) : Option ZoneId :=
  if num = 2 then
    some (.short)
  else if num = 4 then
    some (.full)
  else
    none

end ZoneId

/--
`ZoneName` represents different zone name formats based on the number of pattern letters and
whether daylight saving time is considered.
-/
inductive ZoneName
  /-- Short form of zone name (e.g., "PST") -/
  | short
  /-- Full form of zone name (e.g., "Pacific Standard Time") -/
  | full
  deriving Repr, Inhabited

namespace ZoneName

/--
`classify` classifies the number of pattern letters and the letter type ('z' or 'v')
into a `ZoneName` format.
- For 'z', if less than 4 letters, it returns the short form; if 4 letters, it returns the full form.
- For 'v', if 1 letter, it returns the short form; if 4 letters, it returns the full form.
- Otherwise, it returns none.
-/
def classify (letter : Char) (num : Nat) : Option ZoneName :=
  if letter = 'z' then
    if num < 4 then
      some (.short)
    else if num = 4 then
      some (.full)
    else
      none
  else if letter = 'v' then
    if num = 1 then
      some (.short)
    else if num = 4 then
      some (.full)
    else
      none
  else
    none

end ZoneName

/--
`OffsetX` represents different offset formats based on the number of pattern letters.
The output will vary between the number of pattern letters, whether it's the hour, minute, second,
and whether colons are used.
-/
inductive OffsetX
  /-- Only the hour is output (e.g., "+01") -/
  | hour
  /-- Hour and minute without colon (e.g., "+0130") -/
  | hourMinute
  /-- Hour and minute with colon (e.g., "+01:30") -/
  | hourMinuteColon
  /-- Hour, minute, and second without colon (e.g., "+013015") -/
  | hourMinuteSecond
  /-- Hour, minute, and second with colon (e.g., "+01:30:15") -/
  | hourMinuteSecondColon
  deriving Repr, Inhabited

namespace OffsetX

/--
`classify` classifies the number of pattern letters into an `OffsetX` format.
-/
def classify (num : Nat) : Option OffsetX :=
  if num = 1 then
    some (.hour)
  else if num = 2 then
    some (.hourMinute)
  else if num = 3 then
    some (.hourMinuteColon)
  else if num = 4 then
    some (.hourMinuteSecond)
  else if num = 5 then
    some (.hourMinuteSecondColon)
  else
    none

end OffsetX

/--
`OffsetO` represents localized offset text formats based on the number of pattern letters.
-/
inductive OffsetO
  /-- Short form of the localized offset (e.g., "GMT+8") -/
  | short
  /-- Full form of the localized offset (e.g., "GMT+08:00") -/
  | full
  deriving Repr, Inhabited

namespace OffsetO

/--
`classify` classifies the number of pattern letters into an `OffsetO` format.
-/
def classify (num : Nat) : Option OffsetO :=
  match num with
  | 1 => some (.short)
  | 4 => some (.full)
  | _ => none

end OffsetO

/--
`OffsetZ` represents different offset formats based on the number of pattern letters (capital 'Z').
-/
inductive OffsetZ
  /-- Hour and minute without colon (e.g., "+0130") -/
  | hourMinute
  /-- Localized offset text in full form (e.g., "GMT+08:00") -/
  | full
  /-- Hour, minute, and second with colon (e.g., "+01:30:15") -/
  | hourMinuteSecondColon
  deriving Repr, Inhabited

namespace OffsetZ

/--
`classify` classifies the number of pattern letters into an `OffsetZ` format.
-/
def classify (num : Nat) : Option OffsetZ :=
  match num with
  | 1 | 2 | 3 => some (.hourMinute)
  | 4 => some (.full)
  | 5 => some (.hourMinuteSecondColon)
  | _ => none

end OffsetZ

/--
The `Modifier` inductive type represents various formatting options for date and time components,
matching the format symbols used in date and time strings.
These modifiers can be applied in formatting functions to generate custom date and time outputs.
-/
inductive Modifier
  /--
  `G`: Era (e.g., AD, Anno Domini, A).
  -/
  | G (presentation : Text)

  /--
  `y`: Year of era (e.g., 2004, 04, 0002, 2).
  -/
  | y (presentation : Year)

  /--
  `u`: Year (e.g., 2004, 04, -0001, -1).
  -/
  | u (presentation : Year)

  /--
  `D`: Day of year (e.g., 189).
  -/
  | D (presentation : Number)

  /--
  `M`: Month of year as number or text (e.g., 7, 07, Jul, July, J).
  -/
  | MorL (presentation : Number ⊕ Text)

  /--
  `d`: Day of month (e.g., 10).
  -/
  | d (presentation : Number)

  /--
  `Q`: Quarter of year as number or text (e.g., 3, 03, Q3, 3rd quarter).
  -/
  | Qorq (presentation : Number ⊕ Text)

  /--
  `w`: Week of week-based year (e.g., 27).
  -/
  | w (presentation : Number)

  /--
  `W`: Week of month (e.g., 4).
  -/
  | W (presentation : Number)

  /--
  `E`: Day of week as text (e.g., Tue, Tuesday, T).
  -/
  | E (presentation : Text)

  /--
  `e`: Localized day of week as number or text (e.g., 2, 02, Tue, Tuesday, T).
  -/
  | eorc (presentation : Number ⊕ Text)

  /--
  `F`: Aligned week of month (e.g., 3).
  -/
  | F (presentation : Number)

  /--
  `a`: AM/PM of day (e.g., PM).
  -/
  | a (presentation : Text)

  /--
  `h`: Clock hour of AM/PM (1-12) (e.g., 12).
  -/
  | h (presentation : Number)

  /--
  `K`: Hour of AM/PM (0-11) (e.g., 0).
  -/
  | K (presentation : Number)

  /--
  `k`: Clock hour of day (1-24) (e.g., 24).
  -/
  | k (presentation : Number)

  /--
  `H`: Hour of day (0-23) (e.g., 0).
  -/
  | H (presentation : Number)

  /--
  `m`: Minute of hour (e.g., 30).
  -/
  | m (presentation : Number)

  /--
  `s`: Second of minute (e.g., 55).
  -/
  | s (presentation : Number)

  /--
  `S`: Fraction of second (e.g., 978).
  -/
  | S (presentation : Fraction)

  /--
  `A`: Millisecond of day (e.g., 1234).
  -/
  | A (presentation : Number)

  /--
  `n`: Nanosecond of second (e.g., 987654321).
  -/
  | n (presentation : Number)

  /--
  `N`: Nanosecond of day (e.g., 1234000000).
  -/
  | N (presentation : Number)

  /--
  `V`: Time zone ID (e.g., America/Los_Angeles, Z, -08:30).
  -/
  | V

  /--
  `z`: Time zone name (e.g., Pacific Standard Time, PST).
  -/
  | z (presentation : ZoneName)

  /--
  `O`: Localized zone offset (e.g., GMT+8, GMT+08:00, UTC-08:00).
  -/
  | O (presentation : OffsetO)

  /--
  `X`: Zone offset with 'Z' for zero (e.g., Z, -08, -0830, -08:30).
  -/
  | X (presentation : OffsetX)

  /--
  `x`: Zone offset without 'Z' (e.g., +0000, -08, -0830, -08:30).
  -/
  | x (presentation : OffsetX)

  /--
  `Z`: Zone offset with 'Z' for UTC (e.g., +0000, -0800, -08:00).
  -/
  | Z (presentation : OffsetZ)
  deriving Repr, Inhabited

/--
`abstractParse` abstracts the parsing logic for any type that has a classify function.
It takes a constructor function to build the `Modifier` and a classify function that maps the pattern length to a specific type.
-/
private def parseMod (constructor : α → Modifier) (classify : Nat → Option α) (p : String) : Parser Modifier :=
  let len := p.length
  match classify len with
  | some res => pure (constructor res)
  | none => fail s!"invalid quantity of characters for '{p.get 0}'"

private def parseText (constructor : Text → Modifier) (p : String) : Parser Modifier :=
  parseMod constructor Text.classify p

private def parseFraction (constructor : Fraction → Modifier) (p : String) : Parser Modifier :=
  parseMod constructor Fraction.classify p

private def parseNumber (constructor : Number → Modifier) (p : String) : Parser Modifier :=
  pure (constructor ⟨p.length⟩)

private def parseYear (constructor : Year → Modifier) (p : String) : Parser Modifier :=
  parseMod constructor Year.classify p

private def parseOffsetX (constructor : OffsetX → Modifier) (p : String) : Parser Modifier :=
  parseMod constructor OffsetX.classify p

private def parseOffsetZ (constructor : OffsetZ → Modifier) (p : String) : Parser Modifier :=
  parseMod constructor OffsetZ.classify p

private def parseOffsetO (constructor : OffsetO → Modifier) (p : String) : Parser Modifier :=
  parseMod constructor OffsetO.classify p

private def parseZoneId (p : String) : Parser Modifier :=
  if p.length = 2 then pure .V else fail s!"invalid quantity of characters for '{p.get 0}'"

private def parseNumberText (constructor : (Number ⊕ Text) → Modifier) (p : String) : Parser Modifier :=
  parseMod constructor classifyNumberText p

private def parseZoneName (constructor : ZoneName → Modifier) (p : String) : Parser Modifier :=
  let len := p.length
  match ZoneName.classify (p.get 0) len with
  | some res => pure (constructor res)
  | none => fail s!"invalid quantity of characters for '{p.get 0}'"

private def parseModifier : Parser Modifier
  := (parseText Modifier.G =<< many1Chars (pchar 'G'))
  <|> parseYear Modifier.y =<< many1Chars (pchar 'y')
  <|> parseYear Modifier.u =<< many1Chars (pchar 'u')
  <|> parseNumber Modifier.D =<< many1Chars (pchar 'D')
  <|> parseNumberText Modifier.MorL =<< many1Chars (pchar 'M')
  <|> parseNumberText Modifier.MorL =<< many1Chars (pchar 'L')
  <|> parseNumber Modifier.d =<< many1Chars (pchar 'd')
  <|> parseNumberText Modifier.Qorq =<< many1Chars (pchar 'Q')
  <|> parseNumberText Modifier.Qorq =<< many1Chars (pchar 'q')
  <|> parseNumber Modifier.w =<< many1Chars (pchar 'w')
  <|> parseNumber Modifier.W =<< many1Chars (pchar 'W')
  <|> parseText Modifier.E =<< many1Chars (pchar 'E')
  <|> parseNumberText Modifier.eorc =<< many1Chars (pchar 'e')
  <|> parseNumberText Modifier.eorc =<< many1Chars (pchar 'c')
  <|> parseNumber Modifier.F =<< many1Chars (pchar 'F')
  <|> parseText Modifier.a =<< many1Chars (pchar 'a')
  <|> parseNumber Modifier.h =<< many1Chars (pchar 'h')
  <|> parseNumber Modifier.K =<< many1Chars (pchar 'K')
  <|> parseNumber Modifier.k =<< many1Chars (pchar 'k')
  <|> parseNumber Modifier.H =<< many1Chars (pchar 'H')
  <|> parseNumber Modifier.m =<< many1Chars (pchar 'm')
  <|> parseNumber Modifier.s =<< many1Chars (pchar 's')
  <|> parseFraction Modifier.S =<< many1Chars (pchar 'S')
  <|> parseNumber Modifier.A =<< many1Chars (pchar 'A')
  <|> parseNumber Modifier.n =<< many1Chars (pchar 'n')
  <|> parseNumber Modifier.N =<< many1Chars (pchar 'N')
  <|> parseZoneId =<< many1Chars (pchar 'V')
  <|> parseZoneName Modifier.z =<< many1Chars (pchar 'z')
  <|> parseOffsetO Modifier.O =<< many1Chars (pchar 'O')
  <|> parseOffsetX Modifier.X =<< many1Chars (pchar 'X')
  <|> parseOffsetX Modifier.x =<< many1Chars (pchar 'x')
  <|> parseOffsetZ Modifier.Z =<< many1Chars (pchar 'Z')

/--
The part of a formatting string. A string is just a text and a modifier is in the format described in
the `Modifier` type.
-/
inductive FormatPart
  /--
  A string literal.
  -/
  | string (val : String)

  /--
  A modifier that renders some data into text.
  -/
  | modifier (modifier : Modifier)
  deriving Repr

instance : Coe String FormatPart where
  coe := .string

instance : Coe Modifier FormatPart where
  coe := .modifier

/--
The format of date and time string.
-/
abbrev FormatString := List FormatPart

/--
If the format is aware of some timezone data it parses or if it parses any timezone.
-/
inductive Awareness
  /-- The format only parses a single timezone. -/
  | only : TimeZone → Awareness
  /-- The format parses any timezone. -/
  | any

namespace Awareness

instance : Coe TimeZone Awareness where
  coe := .only

@[simp]
private def type (x : Awareness) : Type :=
  match x with
  | .any => ZonedDateTime
  | .only tz => DateTime tz

instance : Inhabited (type aw) where
  default := by
    simp [type]
    split <;> exact Inhabited.default

private def getD (x : Awareness) (default : TimeZone) : TimeZone :=
  match x with
  | .any => default
  | .only tz => tz

end Awareness

/--
Configuration options for formatting and parsing date/time strings.
-/
structure FormatConfig where
  /--
  Whether to allow leap seconds, such as `2016-12-31T23:59:60Z`.
  Default is `false`.
  -/
  allowLeapSeconds : Bool := false

deriving Inhabited, Repr

/--
A specification on how to format a data or parse some string.
-/
structure GenericFormat (awareness : Awareness) where
  /--
  Configuration options for formatting behavior.
  -/
  config : FormatConfig

  /--
  The format string used for parsing and formatting.
  -/
  string : FormatString
  deriving Inhabited, Repr

private def parseFormatPart : Parser FormatPart
  := (.modifier <$> parseModifier)
  <|> (pchar '\\') *> any <&> (.string ∘ toString)
  <|> (pchar '\"' *>  many1Chars (satisfy (· ≠ '\"')) <* pchar '\"') <&> .string
  <|> (pchar '\'' *>  many1Chars (satisfy (· ≠ '\'')) <* pchar '\'') <&> .string
  <|> many1Chars (satisfy (fun x => ¬Char.isAlpha x ∧ x ≠ '\'' ∧ x ≠ '\"')) <&> .string

private def specParser : Parser FormatString :=
  (Array.toList <$> many parseFormatPart) <* eof

private def specParse (s : String) : Except String FormatString :=
  specParser.run s

-- Pretty printer

private def leftPad (n : Nat) (a : Char) (s : String) : String :=
  "".pushn a (n -  s.length) ++ s

private def rightPad (n : Nat) (a : Char) (s : String) : String :=
  s ++ "".pushn a (n - s.length)

private def pad (size : Nat)  (n : Int) (cut : Bool := false) : String :=
  let (sign, n) := if n < 0 then ("-", -n) else ("", n)

  let numStr := toString n
  if numStr.length > size then
    sign ++ if cut then numStr.drop (numStr.length - size) else numStr
  else
    sign ++ leftPad size '0' numStr

private def rightTruncate (size : Nat)  (n : Int) (cut : Bool := false) : String :=
  let (sign, n) := if n < 0 then ("-", -n) else ("", n)

  let numStr := toString n
  if numStr.length > size then
    sign ++ if cut then numStr.take size else numStr
  else
    sign ++ rightPad size '0' numStr

private def formatMonthLong : Month.Ordinal → String
  | ⟨1, _⟩ => "January"
  | ⟨2, _⟩ => "February"
  | ⟨3, _⟩ => "March"
  | ⟨4, _⟩ => "April"
  | ⟨5, _⟩ => "May"
  | ⟨6, _⟩ => "June"
  | ⟨7, _⟩ => "July"
  | ⟨8, _⟩ => "August"
  | ⟨9, _⟩ => "September"
  | ⟨10, _⟩ => "October"
  | ⟨11, _⟩ => "November"
  | ⟨12, _⟩ => "December"

private def formatMonthShort : Month.Ordinal → String
  | ⟨1, _⟩ => "Jan"
  | ⟨2, _⟩ => "Feb"
  | ⟨3, _⟩ => "Mar"
  | ⟨4, _⟩ => "Apr"
  | ⟨5, _⟩ => "May"
  | ⟨6, _⟩ => "Jun"
  | ⟨7, _⟩ => "Jul"
  | ⟨8, _⟩ => "Aug"
  | ⟨9, _⟩ => "Sep"
  | ⟨10, _⟩ => "Oct"
  | ⟨11, _⟩ => "Nov"
  | ⟨12, _⟩ => "Dec"

private def formatMonthNarrow : Month.Ordinal → String
  | ⟨1, _⟩  => "J"
  | ⟨2, _⟩  => "F"
  | ⟨3, _⟩  => "M"
  | ⟨4, _⟩  => "A"
  | ⟨5, _⟩  => "M"
  | ⟨6, _⟩  => "J"
  | ⟨7, _⟩  => "J"
  | ⟨8, _⟩  => "A"
  | ⟨9, _⟩  => "S"
  | ⟨10, _⟩ => "O"
  | ⟨11, _⟩ => "N"
  | ⟨12, _⟩ => "D"

private def formatWeekdayLong : Weekday → String
  | .sunday => "Sunday"
  | .monday => "Monday"
  | .tuesday => "Tuesday"
  | .wednesday => "Wednesday"
  | .thursday => "Thursday"
  | .friday => "Friday"
  | .saturday => "Saturday"

private def formatWeekdayShort : Weekday → String
  | .sunday => "Sun"
  | .monday => "Mon"
  | .tuesday => "Tue"
  | .wednesday => "Wed"
  | .thursday => "Thu"
  | .friday => "Fri"
  | .saturday => "Sat"

private def formatWeekdayNarrow : Weekday → String
  | .sunday => "S"
  | .monday => "M"
  | .tuesday => "T"
  | .wednesday => "W"
  | .thursday => "T"
  | .friday => "F"
  | .saturday => "S"

private def formatEraShort : Year.Era → String
  | .bce => "BCE"
  | .ce  => "CE"

private def formatEraLong : Year.Era → String
  | .bce => "Before Common Era"
  | .ce  => "Common Era"

private def formatEraNarrow : Year.Era → String
  | .bce => "B"
  | .ce  => "C"

private def formatQuarterNumber : Month.Quarter → String
  |⟨1, _⟩ => "1"
  |⟨2, _⟩ => "2"
  |⟨3, _⟩ => "3"
  |⟨4, _⟩ => "4"

private def formatQuarterShort : Month.Quarter → String
  | ⟨1, _⟩ => "Q1"
  | ⟨2, _⟩ => "Q2"
  | ⟨3, _⟩ => "Q3"
  | ⟨4, _⟩ => "Q4"

private def formatQuarterLong : Month.Quarter → String
  | ⟨1, _⟩ => "1st quarter"
  | ⟨2, _⟩ => "2nd quarter"
  | ⟨3, _⟩ => "3rd quarter"
  | ⟨4, _⟩ => "4th quarter"

private def formatMarkerShort (marker : HourMarker) : String :=
  match marker with
  | .am => "AM"
  | .pm => "PM"

private def formatMarkerLong (marker : HourMarker) : String :=
  match marker with
  | .am => "Ante Meridiem"
  | .pm => "Post Meridiem"

private def formatMarkerNarrow (marker : HourMarker) : String :=
  match marker with
  | .am => "A"
  | .pm => "P"

private def toSigned (data : Int) : String :=
  if data < 0 then toString data else "+" ++ toString data

private def toIsoString (offset : Offset) (withMinutes : Bool) (withSeconds : Bool) (colon : Bool) : String :=
  let (sign, time) := if offset.second.val ≥ 0 then ("+", offset.second) else ("-", -offset.second)
  let time := PlainTime.ofSeconds time
  let pad := leftPad 2 '0' ∘ toString

  let data := s!"{sign}{pad time.hour.val}"
  let data := if withMinutes then s!"{data}{if colon then ":" else ""}{pad time.minute.val}" else data
  let data := if withSeconds ∧ time.second.val ≠ 0 then s!"{data}{if colon then ":" else ""}{pad time.second.val}" else data

  data

private def TypeFormat : Modifier → Type
  | .G _ => Year.Era
  | .y _ => Year.Offset
  | .u _ => Year.Offset
  | .D _ => Sigma Day.Ordinal.OfYear
  | .MorL _ => Month.Ordinal
  | .d _ => Day.Ordinal
  | .Qorq _ => Month.Quarter
  | .w _ => Week.Ordinal
  | .W _ => Week.Ordinal.OfMonth
  | .E _ => Weekday
  | .eorc _ => Weekday
  | .F _ => Bounded.LE 1 5
  | .a _ => HourMarker
  | .h _ => Bounded.LE 1 12
  | .K _ => Bounded.LE 0 11
  | .k _ => Bounded.LE 1 24
  | .H _ => Hour.Ordinal
  | .m _ => Minute.Ordinal
  | .s _ => Second.Ordinal true
  | .S _ => Nanosecond.Ordinal
  | .A _ => Millisecond.Offset
  | .n _ => Nanosecond.Ordinal
  | .N _ => Nanosecond.Offset
  | .V => String
  | .z _ => String
  | .O _ => Offset
  | .X _ => Offset
  | .x _ => Offset
  | .Z _ => Offset

private def formatWith (modifier : Modifier) (data: TypeFormat modifier) : String :=
  match modifier with
  | .G format =>
    match format with
    | .short => formatEraShort data
    | .full => formatEraLong data
    | .narrow => formatEraNarrow data
  | .y format =>
    let info := data.toInt
    let info := if info ≤ 0 then -info + 1 else info
    match format with
    | .any => pad 0 (data.toInt)
    | .twoDigit => pad 2 (info % 100)
    | .fourDigit => pad 4 info
    | .extended n => pad n info
  | .u format =>
    match format with
    | .any => pad 0 (data.toInt)
    | .twoDigit => pad 2 (data.toInt % 100)
    | .fourDigit => pad 4 data.toInt
    | .extended n => pad n data.toInt
  | .D format =>
    pad format.padding data.snd.val
  | .MorL format =>
    match format with
    | .inl format => pad format.padding data.val
    | .inr .short => formatMonthShort data
    | .inr .full => formatMonthLong data
    | .inr .narrow => formatMonthNarrow data
  | .d format =>
    pad format.padding data.val
  | .Qorq format =>
    match format with
    | .inl format => pad format.padding data.val
    | .inr .short => formatQuarterShort data
    | .inr .full => formatQuarterLong data
    | .inr .narrow => formatQuarterNumber data
  | .w format =>
    pad format.padding data.val
  | .W format =>
    pad format.padding data.val
  | .E format =>
    match format with
    | .short => formatWeekdayShort data
    | .full => formatWeekdayLong data
    | .narrow => formatWeekdayNarrow data
  | .eorc format =>
    match format with
    | .inl format => pad format.padding data.toOrdinal.val
    | .inr .short => formatWeekdayShort data
    | .inr .full => formatWeekdayLong data
    | .inr .narrow => formatWeekdayNarrow data
  | .F format =>
    pad format.padding data.val
  | .a format =>
    match format with
    | .short => formatMarkerShort data
    | .full => formatMarkerLong data
    | .narrow => formatMarkerNarrow data
  | .h format => pad format.padding (data.val % 12)
  | .K format => pad format.padding (data.val % 12)
  | .k format => pad format.padding data.val
  | .H format => pad format.padding data.val
  | .m format => pad format.padding data.val
  | .s format => pad format.padding data.val
  | .S format =>
    match format with
    | .nano => pad 9 data.val
    | .truncated n => rightTruncate n data.val (cut := true)
  | .A format =>
    pad format.padding data.val
  | .n format =>
    pad format.padding data.val
  | .N format =>
    pad format.padding data.val
  | .V => data
  | .z format =>
    match format with
    | .short => data
    | .full => data
  | .O format =>
    match format with
    | .short => s!"GMT{toSigned data.second.toHours.toInt}"
    | .full => s!"GMT{toIsoString data true false true}"
  | .X format =>
    if data.second == 0 then
      "Z"
    else
      match format with
        | .hour => toIsoString data false false false
        | .hourMinute => toIsoString data true false false
        | .hourMinuteColon => toIsoString data true false true
        | .hourMinuteSecond => toIsoString data true true false
        | .hourMinuteSecondColon => toIsoString data true true true
  | .x format =>
    match format with
    | .hour =>
      toIsoString data (data.second.toMinutes.val % 60 ≠ 0) false false
    | .hourMinute =>
      toIsoString data true false false
    | .hourMinuteColon =>
      toIsoString data true (data.second.val % 60 ≠ 0) true
    | .hourMinuteSecond =>
      toIsoString data true (data.second.val % 60 ≠ 0) false
    | .hourMinuteSecondColon =>
      toIsoString data true true true
  | .Z format =>
    match format with
    | .hourMinute =>
      toIsoString data true false false
    | .full =>
      if data.second.val = 0
        then "GMT"
        else s!"GMT{toIsoString data true false true}"
    | .hourMinuteSecondColon =>
      if data.second == 0
        then "Z"
        else  toIsoString data true (data.second.val % 60 ≠ 0) true

private def dateFromModifier (date : DateTime tz) : TypeFormat modifier :=
  match modifier with
  | .G _ => date.era
  | .y _ => date.year
  | .u _ => date.year
  | .D _ => Sigma.mk _ date.dayOfYear
  | .MorL _ => date.month
  | .d _ => date.day
  | .Qorq _ => date.quarter
  | .w _ => date.weekOfYear
  | .W _ => date.alignedWeekOfMonth
  | .E _ =>  date.weekday
  | .eorc _ => date.weekday
  | .F _ => date.weekOfMonth
  | .a _ => HourMarker.ofOrdinal date.hour
  | .h _ => HourMarker.toRelative date.hour |>.fst
  | .K _ => date.hour.emod 12 (by decide)
  | .k _ => date.hour.shiftTo1BasedHour
  | .H _ => date.hour
  | .m _ => date.minute
  | .s _ => date.date.get.time.second
  | .S _ => date.nanosecond
  | .A _ => date.date.get.time.toMilliseconds
  | .n _ => date.nanosecond
  | .N _ => date.date.get.time.toNanoseconds
  | .V => tz.name
  | .z .short => tz.abbreviation
  | .z .full => tz.name
  | .O _ => tz.offset
  | .X _ => tz.offset
  | .x _ => tz.offset
  | .Z _ => tz.offset

private def parseMonthLong : Parser Month.Ordinal
   := pstring "January" *> pure ⟨1, by decide⟩
  <|> pstring "February" *> pure ⟨2, by decide⟩
  <|> pstring "March" *> pure ⟨3, by decide⟩
  <|> pstring "April" *> pure ⟨4, by decide⟩
  <|> pstring "May" *> pure ⟨5, by decide⟩
  <|> pstring "June" *> pure ⟨6, by decide⟩
  <|> pstring "July" *> pure ⟨7, by decide⟩
  <|> pstring "August" *> pure ⟨8, by decide⟩
  <|> pstring "September" *> pure ⟨9, by decide⟩
  <|> pstring "October" *> pure ⟨10, by decide⟩
  <|> pstring "November" *> pure ⟨11, by decide⟩
  <|> pstring "December" *> pure ⟨12, by decide⟩

/--
Parses a short value of a `Month.Ordinal`
-/
def parseMonthShort : Parser Month.Ordinal
   := pstring "Jan" *> pure ⟨1, by decide⟩
  <|> pstring "Feb" *> pure ⟨2, by decide⟩
  <|> pstring "Mar" *> pure ⟨3, by decide⟩
  <|> pstring "Apr" *> pure ⟨4, by decide⟩
  <|> pstring "May" *> pure ⟨5, by decide⟩
  <|> pstring "Jun" *> pure ⟨6, by decide⟩
  <|> pstring "Jul" *> pure ⟨7, by decide⟩
  <|> pstring "Aug" *> pure ⟨8, by decide⟩
  <|> pstring "Sep" *> pure ⟨9, by decide⟩
  <|> pstring "Oct" *> pure ⟨10, by decide⟩
  <|> pstring "Nov" *> pure ⟨11, by decide⟩
  <|> pstring "Dec" *> pure ⟨12, by decide⟩

private def parseMonthNarrow : Parser Month.Ordinal
   := pstring "J" *> pure ⟨1, by decide⟩
  <|> pstring "F" *> pure ⟨2, by decide⟩
  <|> pstring "M" *> pure ⟨3, by decide⟩
  <|> pstring "A" *> pure ⟨4, by decide⟩
  <|> pstring "M" *> pure ⟨5, by decide⟩
  <|> pstring "J" *> pure ⟨6, by decide⟩
  <|> pstring "J" *> pure ⟨7, by decide⟩
  <|> pstring "A" *> pure ⟨8, by decide⟩
  <|> pstring "S" *> pure ⟨9, by decide⟩
  <|> pstring "O" *> pure ⟨10, by decide⟩
  <|> pstring "N" *> pure ⟨11, by decide⟩
  <|> pstring "D" *> pure ⟨12, by decide⟩

private def parseWeekdayLong : Parser Weekday
   := pstring "Sunday" *> pure Weekday.sunday
  <|> pstring "Monday" *> pure Weekday.monday
  <|> pstring "Tuesday" *> pure Weekday.tuesday
  <|> pstring "Wednesday" *> pure Weekday.wednesday
  <|> pstring "Thursday" *> pure Weekday.thursday
  <|> pstring "Friday" *> pure Weekday.friday
  <|> pstring "Saturday" *> pure Weekday.saturday

private def parseWeekdayShort : Parser Weekday
   := pstring "Sun" *> pure Weekday.sunday
  <|> pstring "Mon" *> pure Weekday.monday
  <|> pstring "Tue" *> pure Weekday.tuesday
  <|> pstring "Wed" *> pure Weekday.wednesday
  <|> pstring "Thu" *> pure Weekday.thursday
  <|> pstring "Fri" *> pure Weekday.friday
  <|> pstring "Sat" *> pure Weekday.saturday

private def parseWeekdayNarrow : Parser Weekday
   := pstring "S" *> pure Weekday.sunday
  <|> pstring "M" *> pure Weekday.monday
  <|> pstring "T" *> pure Weekday.tuesday
  <|> pstring "W" *> pure Weekday.wednesday
  <|> pstring "T" *> pure Weekday.thursday
  <|> pstring "F" *> pure Weekday.friday
  <|> pstring "S" *> pure Weekday.saturday

private def parseEraShort : Parser Year.Era
   := pstring "BCE" *> pure Year.Era.bce
  <|> pstring "CE" *> pure Year.Era.ce

private def parseEraLong : Parser Year.Era
   := pstring "Before Common Era" *> pure Year.Era.bce
  <|> pstring "Common Era" *> pure Year.Era.ce

private def parseEraNarrow : Parser Year.Era
   := pstring "B" *> pure Year.Era.bce
  <|> pstring "C" *> pure Year.Era.ce

private def parseQuarterNumber : Parser Month.Quarter
   := pstring "1" *> pure ⟨1, by decide⟩
  <|> pstring "2" *> pure ⟨2, by decide⟩
  <|> pstring "3" *> pure ⟨3, by decide⟩
  <|> pstring "4" *> pure ⟨4, by decide⟩

private def parseQuarterLong : Parser Month.Quarter
   := pstring "1st quarter" *> pure ⟨1, by decide⟩
  <|> pstring "2nd quarter" *> pure ⟨2, by decide⟩
  <|> pstring "3rd quarter" *> pure ⟨3, by decide⟩
  <|> pstring "4th quarter" *> pure ⟨4, by decide⟩

private def parseQuarterShort : Parser Month.Quarter
   := pstring "Q1" *> pure ⟨1, by decide⟩
  <|> pstring "Q2" *> pure ⟨2, by decide⟩
  <|> pstring "Q3" *> pure ⟨3, by decide⟩
  <|> pstring "Q4" *> pure ⟨4, by decide⟩

private def parseMarkerShort : Parser HourMarker
   := pstring "AM" *> pure HourMarker.am
  <|> pstring "PM" *> pure HourMarker.pm

private def parseMarkerLong : Parser HourMarker
   := pstring "Ante Meridiem" *> pure HourMarker.am
  <|> pstring "Post Meridiem" *> pure HourMarker.pm

private def parseMarkerNarrow : Parser HourMarker
   := pstring "A" *> pure HourMarker.am
  <|> pstring "P" *> pure HourMarker.pm

private def exactly (parse : Parser α) (size : Nat) : Parser (Array α) :=
  let rec go (acc : Array α) (count : Nat) : Parser (Array α) :=
    if count ≥ size then
      pure acc
    else do
      let res ← parse
      go (acc.push res) count.succ
  termination_by size - count

  go #[] 12

private def exactlyChars (parse : Parser Char) (size : Nat) : Parser String :=
  let rec go (acc : String) (count : Nat) : Parser String :=
    if count ≥ size then
      pure acc
    else do
      let res ← parse
      go (acc.push res) count.succ
  termination_by size - count

  go "" 0

private def parseSigned (parser : Parser Nat) : Parser Int := do
  let signed ← optional (pstring "-")
  let res ← parser
  return if signed.isSome then -res else res

private def parseNum (size : Nat) : Parser Nat :=
  String.toNat! <$> exactlyChars (satisfy Char.isDigit) size

private def parseAtLeastNum (size : Nat) : Parser Nat :=
  String.toNat! <$> do
    let start ← exactlyChars (satisfy Char.isDigit) size
    let end_ ← manyChars (satisfy Char.isDigit)
    pure (start ++ end_)

private def parseFlexibleNum (size : Nat) : Parser Nat :=
  if size = 1 then parseAtLeastNum 1 else parseNum size

private def parseFractionNum (size : Nat) (pad : Nat) : Parser Nat :=
  String.toNat! <$> rightPad pad '0' <$> exactlyChars (satisfy Char.isDigit) size

private def parseIdentifier : Parser String :=
  many1Chars (satisfy (fun x => x.isAlpha ∨ x.isDigit ∨ x = '_' ∨ x = '-' ∨ x = '/'))

private def parseNatToBounded { n m : Nat } (parser : Parser Nat) : Parser (Bounded.LE n m) := do
  let res ← parser
  if h : n ≤ res ∧ res ≤ m then
    return Bounded.LE.ofNat' res h
  else
    fail s!"need a natural number in the interval of {n} to {m}"

private inductive Reason
  | yes
  | no
  | optional

private def parseOffset (withMinutes : Reason) (withSeconds : Reason) (withColon : Bool) : Parser Offset := do
  let sign ← (pchar '+' *> pure 1) <|> (pchar '-' *> pure (-1))
  let hours : Hour.Offset ← UnitVal.ofInt <$> parseNum 2

  if hours.val < 0 ∨ hours.val > 23 then
    fail s!"invalid hour offset: {hours.val}. Must be between 0 and 23."

  let colon := if withColon then pchar ':' else pure ':'

  let parseUnit {n} (reason : Reason) : Parser (Option (UnitVal n)) :=
    match reason with
    | .yes => some <$> (colon *> UnitVal.ofInt <$> parseNum 2)
    | .no => pure none
    | .optional => optional (colon *> UnitVal.ofInt <$> parseNum 2)

  let minutes : Option Minute.Offset ← parseUnit withMinutes

  if let some m := minutes then
    if m.val > 59 then
      fail s!"invalid minute offset: {m.val}. Must be between 0 and 59."

  let seconds : Option Second.Offset ← parseUnit withSeconds

  if let some s := seconds then
    if s.val > 59 then
      fail s!"invalid second offset: {s.val}. Must be between 0 and 59."

  let hours := hours.toSeconds + (minutes.getD 0).toSeconds + (seconds.getD 0)

  return Offset.ofSeconds ⟨hours.val * sign⟩

private def parseWith (config : FormatConfig) : (mod : Modifier) → Parser (TypeFormat mod)
  | .G format =>
    match format with
    | .short => parseEraShort
    | .full => parseEraLong
    | .narrow => parseEraNarrow
  | .y format =>
    match format with
    | .any => Int.ofNat <$> parseAtLeastNum 1
    | .twoDigit => (2000 + ·) <$> Int.ofNat <$> parseNum 2
    | .fourDigit => Int.ofNat <$> parseNum 4
    | .extended n => Int.ofNat <$> parseNum n
  | .u format =>
    match format with
    | .any => parseSigned <| parseAtLeastNum 1
    | .twoDigit => (2000 + ·) <$> Int.ofNat <$> parseNum 2
    | .fourDigit => parseSigned <| parseNum 4
    | .extended n => parseSigned <| parseNum n
  | .D format => Sigma.mk true <$> parseNatToBounded (parseFlexibleNum format.padding)
  | .MorL format =>
    match format with
    | .inl format => parseNatToBounded (parseFlexibleNum format.padding)
    | .inr .short => parseMonthShort
    | .inr .full => parseMonthLong
    | .inr .narrow => parseMonthNarrow
  | .d format => parseNatToBounded (parseFlexibleNum format.padding)
  | .Qorq format =>
    match format with
    | .inl format => parseNatToBounded (parseFlexibleNum format.padding)
    | .inr .short => parseQuarterShort
    | .inr .full => parseQuarterLong
    | .inr .narrow => parseQuarterNumber
  | .w format => parseNatToBounded (parseFlexibleNum format.padding)
  | .W format => parseNatToBounded (parseFlexibleNum format.padding)
  | .E format =>
    match format with
    | .short => parseWeekdayShort
    | .full => parseWeekdayLong
    | .narrow => parseWeekdayNarrow
  | .eorc format =>
    match format with
    | .inl format => Weekday.ofOrdinal <$> parseNatToBounded (parseFlexibleNum format.padding)
    | .inr .short => parseWeekdayShort
    | .inr .full => parseWeekdayLong
    | .inr .narrow => parseWeekdayNarrow
  | .F format => parseNatToBounded (parseFlexibleNum format.padding)
  | .a format =>
    match format with
    | .short => parseMarkerShort
    | .full => parseMarkerLong
    | .narrow => parseMarkerNarrow
  | .h format => parseNatToBounded (parseFlexibleNum format.padding)
  | .K format => parseNatToBounded (parseFlexibleNum format.padding)
  | .k format => parseNatToBounded (parseFlexibleNum format.padding)
  | .H format => parseNatToBounded (parseFlexibleNum format.padding)
  | .m format => parseNatToBounded (parseFlexibleNum format.padding)
  | .s format =>
    if config.allowLeapSeconds then
      parseNatToBounded (parseFlexibleNum format.padding)
    else do
      let res : Bounded.LE 0 59 ← parseNatToBounded (parseFlexibleNum format.padding)
      return res.expandTop (by decide)
  | .S format =>
    match format with
    | .nano => parseNatToBounded (parseFlexibleNum 9)
    | .truncated n => parseNatToBounded (parseFractionNum n 9)
  | .A format => Millisecond.Offset.ofNat <$> (parseFlexibleNum format.padding)
  | .n format => parseNatToBounded (parseFlexibleNum format.padding)
  | .N format => Nanosecond.Offset.ofNat <$> (parseFlexibleNum format.padding)
  | .V => parseIdentifier
  | .z format =>
    match format with
    | .short => parseIdentifier
    | .full => parseIdentifier
  | .O format =>
    match format with
    | .short => pstring "GMT" *> parseOffset .no .no false
    | .full => pstring "GMT" *> parseOffset .yes .optional false
  | .X format =>
    let p : Parser Offset :=
      match format with
        | .hour => parseOffset .no .no false
        | .hourMinute => parseOffset .yes .no false
        | .hourMinuteColon => parseOffset .yes .no true
        | .hourMinuteSecond => parseOffset .yes .yes false
        | .hourMinuteSecondColon => parseOffset .yes .yes true
    p <|> (pstring "Z" *> pure (Offset.ofSeconds 0))
  | .x format =>
    match format with
    | .hour =>
      parseOffset .optional .no false
    | .hourMinute =>
      parseOffset .yes .no false
    | .hourMinuteColon =>
      parseOffset .yes .optional true
    | .hourMinuteSecond =>
      parseOffset .yes .optional false
    | .hourMinuteSecondColon =>
      parseOffset .yes .yes true
  | .Z format =>
    match format with
    | .hourMinute =>
      parseOffset .yes .no false
    | .full => do
      skipString "GMT"
      let res ← optional (parseOffset .yes .no true)
      return res.getD Offset.zero
    | .hourMinuteSecondColon =>
      (skipString "Z" *> pure Offset.zero)
      <|> (parseOffset .yes .optional true)

private def formatPartWithDate (date : DateTime tz) (part : FormatPart) : String :=
  match part with
  | .modifier mod => formatWith mod (dateFromModifier date)
  | .string s => s

@[simp]
private def FormatType (result : Type) : FormatString → Type
  | .modifier entry :: xs => (TypeFormat entry) → (FormatType result xs)
  | .string _ :: xs => (FormatType result xs)
  | [] => result

namespace GenericFormat

private structure DateBuilder where
  G : Option Year.Era := none
  y : Option Year.Offset := none
  u : Option Year.Offset := none
  D : Option (Sigma Day.Ordinal.OfYear) := none
  MorL : Option Month.Ordinal := none
  d : Option Day.Ordinal := none
  Qorq : Option Month.Quarter := none
  w : Option Week.Ordinal := none
  W : Option Week.Ordinal.OfMonth := none
  E : Option Weekday := none
  eorc : Option Weekday := none
  F : Option (Bounded.LE 1 5) := none
  a : Option HourMarker := none
  h : Option (Bounded.LE 1 12) := none
  K : Option (Bounded.LE 0 11) := none
  k : Option (Bounded.LE 1 24) := none
  H : Option Hour.Ordinal := none
  m : Option Minute.Ordinal := none
  s : Option (Second.Ordinal true) := none
  S : Option Nanosecond.Ordinal := none
  A : Option Millisecond.Offset := none
  n : Option Nanosecond.Ordinal := none
  N : Option Nanosecond.Offset := none
  V : Option String := none
  z : Option String := none
  zabbrev : Option String := none
  O : Option Offset := none
  X : Option Offset := none
  x : Option Offset := none
  Z : Option Offset := none

namespace DateBuilder

private def insert (date : DateBuilder) (modifier : Modifier) (data : TypeFormat modifier) : DateBuilder :=
  match modifier with
  | .G _ => { date with G := some data }
  | .y _ => { date with y := some data }
  | .u _ => { date with u := some data }
  | .D _ => { date with D := some data }
  | .MorL _ => { date with MorL := some data }
  | .d _ => { date with d := some data }
  | .Qorq _ => { date with Qorq := some data }
  | .w _ => { date with w := some data }
  | .W _ => { date with W := some data }
  | .E _ => { date with E := some data }
  | .eorc _ => { date with eorc := some data }
  | .F _ => { date with F := some data }
  | .a _ => { date with a := some data }
  | .h _ => { date with h := some data }
  | .K _ => { date with K := some data }
  | .k _ => { date with k := some data }
  | .H _ => { date with H := some data }
  | .m _ => { date with m := some data }
  | .s _ => { date with s := some data }
  | .S _ => { date with S := some data }
  | .A _ => { date with A := some data }
  | .n _ => { date with n := some data }
  | .N _ => { date with N := some data }
  | .V => { date with V := some data }
  | .z .full => { date with z := some data }
  | .z .short => { date with zabbrev := some data }
  | .O _ => { date with O := some data }
  | .X _ => { date with X := some data }
  | .x _ => { date with x := some data }
  | .Z _ => { date with Z := some data }

private def convertYearAndEra (year : Year.Offset) : Year.Era → Year.Offset
  | .ce => year
  | .bce => -(year + 1)

private def build (builder : DateBuilder) (aw : Awareness) : Option aw.type :=
  let offset := builder.O <|> builder.X <|> builder.x <|> builder.Z |>.getD Offset.zero

  let tz : TimeZone := {
    offset,
    name := builder.V <|> builder.z |>.getD (offset.toIsoString true),
    abbreviation := builder.zabbrev |>.getD (offset.toIsoString true),
    isDST := false,
  }

  let month := builder.MorL |>.getD 0
  let day := builder.d |>.getD 0
  let era := (builder.G.getD .ce)

  let year
    := builder.u
    <|> ((convertYearAndEra · era) <$> builder.y)
    |>.getD 0

  let hour : Option (Bounded.LE 0 23) :=
    if let some marker := builder.a then
      marker.toAbsolute <$> builder.h
      <|> marker.toAbsolute <$> ((Bounded.LE.add · 1) <$> builder.K)
    else
      none

  let hour :=
    hour <|> (
      let one : Option (Bounded.LE 0 23) := builder.H
      let other : Option (Bounded.LE 0 23) := (Bounded.LE.sub · 1) <$> builder.k
      (one <|> other))
      |>.getD ⟨0, by decide⟩

  let minute := builder.m |>.getD 0
  let second := builder.s |>.getD 0
  let nano := (builder.n <|> builder.S) |>.getD 0

  let time
    :=  PlainTime.ofNanoseconds <$> builder.N
    <|> PlainTime.ofMilliseconds <$> builder.A
    |>.getD (PlainTime.mk hour minute second nano)

  let datetime : Option PlainDateTime :=
    if valid : year.Valid month day then
      let date : PlainDate := { year, month, day, valid }
      some { date, time }
    else
      none

  match aw with
    | .only newTz => (ofPlainDateTime · newTz) <$> datetime
    | .any => (ZonedDateTime.ofPlainDateTime · (ZoneRules.ofTimeZone tz)) <$> datetime

end DateBuilder

private def parseWithDate (date : DateBuilder) (config : FormatConfig) (mod : FormatPart) : Parser DateBuilder := do
  match mod with
  | .modifier s => do
    let res ← parseWith config s
    return date.insert s res
  | .string s => pstring s *> pure date

/--
Constructs a new `GenericFormat` specification for a date-time string. Modifiers can be combined to create
custom formats, such as "YYYY, MMMM, D".
-/
def spec (input : String) (config : FormatConfig := {}) : Except String (GenericFormat tz) := do
  let string ← specParser.run input
  return ⟨config, string⟩

/--
Builds a `GenericFormat` from the input string. If parsing fails, it will panic
-/
def spec! (input : String) (config : FormatConfig := {}) : GenericFormat tz :=
  match specParser.run input with
  | .ok res => ⟨config, res⟩
  | .error res => panic! res

/--
Formats a `DateTime` value into a string using the given `GenericFormat`.
-/
def format (format : GenericFormat aw) (date : DateTime tz) : String :=
  let mapper (part : FormatPart) :=
    match aw with
    | .any => formatPartWithDate date part
    | .only tz => formatPartWithDate (date.convertTimeZone tz) part

  format.string.map mapper
  |> String.join

private def parser (format : FormatString) (config : FormatConfig) (aw : Awareness) : Parser (aw.type) :=
  let rec go (builder : DateBuilder) (x : FormatString) : Parser aw.type :=
    match x with
    | x :: xs => parseWithDate builder config x >>= (go · xs)
    | [] =>
      match builder.build aw with
      | some res => pure res
      | none => fail "could not parse the date"
  go {} format

/--
Parser for a format with a builder.
-/
def builderParser (format: FormatString) (config : FormatConfig) (func: FormatType (Option α) format) : Parser α :=
  let rec go (format : FormatString) (func: FormatType (Option α) format) : Parser α :=
    match format with
    | .modifier x :: xs => do
      let res ← parseWith config x
      go xs (func res)
    | .string s :: xs => skipString s *> (go xs func)
    | [] =>
        match func with
        | some res => eof *> pure res
        | none => fail "invalid date."
  go format func

/--
Parses the input string into a `ZoneDateTime`.
-/
def parse (format : GenericFormat aw) (input : String) : Except String aw.type :=
  (parser format.string format.config aw <* eof).run input

/--
Parses the input string into a `ZoneDateTime` and panics if its wrong.
-/
def parse! (format : GenericFormat aw) (input : String) : aw.type :=
  match parse format input with
  | .ok res => res
  | .error err => panic! err

/--
Parses an input string using a builder function to produce a value.
-/
def parseBuilder (format : GenericFormat aw)  (builder : FormatType (Option α) format.string) (input : String) : Except String α :=
  (builderParser format.string format.config builder).run input

/--
Parses an input string using a builder function, panicking on errors.
-/
def parseBuilder! [Inhabited α] (format : GenericFormat aw)  (builder : FormatType (Option α) format.string) (input : String) : α :=
  match parseBuilder format builder input with
  | .ok res => res
  | .error err => panic! err

/--
Formats the date using the format into a String, using a `getInfo` function to get the information needed to build the `String`.
-/
def formatGeneric (format : GenericFormat aw) (getInfo : (typ : Modifier) → Option (TypeFormat typ)) : Option String :=
  let rec go (data : String) : (format : FormatString) → Option String
    | .modifier x :: xs => do go (data ++ formatWith x (← getInfo x)) xs
    | .string x :: xs => go (data ++ x) xs
    | [] => data
  go "" format.string

/--
Constructs a `FormatType` function to format a date into a string using a `GenericFormat`.
-/
def formatBuilder (format : GenericFormat aw) : FormatType String format.string :=
  let rec go (data : String) : (format : FormatString) → FormatType String format
    | .modifier x :: xs => fun res => go (data ++ formatWith x res) xs
    | .string x :: xs => go (data ++ x) xs
    | [] => data
  go "" format.string

end GenericFormat

/--
Typeclass for formatting and parsing values with the given format type.
-/
class Format (f : Type) (typ : Type → f → Type) where
  /--
  Converts a format `f` into a string.
  -/
  format : (fmt : f) → typ String fmt

  /--
  Parses a string into a format using the provided format type `f`.
  -/
  parse : (fmt : f) → typ (Option α) fmt → String → Except String α

instance : Format (GenericFormat aw) (FormatType · ·.string) where
  format := GenericFormat.formatBuilder
  parse := GenericFormat.parseBuilder

end Time
