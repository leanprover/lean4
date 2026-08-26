/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Time.Zoned
import Init.Data.String.Search

public section

/-!
This module defines the `Modifier` type and its sub-types, representing format pattern letters.
-/

namespace Std
namespace Time
open Std.Time.Internal
open Std.Internal.Parsec.String
open Std.Internal.Parsec Lean PlainTime PlainDate TimeZone DateTime

set_option linter.all true

/--
`Text` represents different text formatting styles.
-/
inductive Text

  /--
  Short form (e.g., "Tue")
  -/
  | short

  /--
  Full form (e.g., "Tuesday")
  -/
  | full

  /--
  Narrow form (e.g., "T")
  -/
  | narrow

  /--
  Two-letter short form (e.g., "Tu"). Produced only by 6-letter weekday patterns (`EEEEEE`, `eeeeee`, `cccccc`).
  -/
  | twoLetterShort
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
  Minimum number of digits; output is zero-padded on the left to reach this width. Determined by the count of pattern letters.
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

  /--
  Nanosecond precision (up to 9 digits)
  -/
  | nano

  /--
  Truncated to `digits` digits (truncated, not rounded)
  -/
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

  /--
  Any size (e.g., "19000000000000")
  -/
  | any

  /--
  Two-digit year format (e.g., "23" for 2023)
  -/
  | twoDigit

  /--
  Four-digit year format (e.g., "2023")
  -/
  | fourDigit

  /--
  Extended year format for more than 4 digits (e.g., "002023")
  -/
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

  /--
  Unknown zone placeholder (1 letter, `V`): always formats as "unk".
  -/
  | unknown

  /--
  IANA time zone ID (2 letters, `VV`, e.g., "America/Los_Angeles").
  -/
  | short

  /--
  Reserved for a future generic location format (`VVVV`). Currently formatted identically to `short`.
  -/
  | full
  deriving Repr, Inhabited

namespace ZoneId

/--
`classify` classifies the number of pattern letters into a `ZoneId` format.
- If 1 letter, it returns the unknown form.
- If 2 letters, it returns the short form.
- If 4 letters, it returns the full form.
- Otherwise, it returns none.
-/
def classify (num : Nat) : Option ZoneId :=
  if num = 1 then
    some (.unknown)
  else if num = 2 then
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
  /--
  Short form of zone name (e.g., "PST")
  -/
  | short
  /--
  Full form of zone name (e.g., "Pacific Standard Time")
  -/
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

  /--
  Only the hour is output (e.g., "+01")
  -/
  | hour

  /--
  Hour and minute without colon (e.g., "+0130")
  -/
  | hourMinute

  /--
  Hour and minute with colon (e.g., "+01:30")
  -/
  | hourMinuteColon

  /--
  Hour, minute, and second without colon (e.g., "+013015")
  -/
  | hourMinuteSecond

  /--
  Hour, minute, and second with colon (e.g., "+01:30:15")
  -/
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

  /--
  Short form of the localized offset (e.g., "GMT+8")
  -/
  | short

  /--
  Full form of the localized offset (e.g., "GMT+08:00")
  -/
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

  /--
  Hour and minute without colon, with optional seconds (e.g., "+0130", "+013015")
  -/
  | hourMinute

  /--
  Localized offset text in full form (e.g., "GMT+08:00")
  -/
  | full

  /--
  Hour and minute with colon, with optional seconds, and "Z" for zero offset (e.g., "+01:30", "+01:30:15", "Z")
  -/
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
`DayPeriod` extends `HourMarker` with exact noon and midnight values, used by the `b` pattern.
-/
inductive DayPeriod

  /--
  Ante meridiem (before noon)
  -/
  | am

  /--
  Post meridiem (after noon)
  -/
  | pm

  /--
  Exactly noon (12:00:00)
  -/
  | noon

  /--
  Exactly midnight (00:00:00)
  -/
  | midnight
  deriving Repr, Inhabited

/--
`ExtendedDayPeriod` is a more granular day-period classification used by the `B` pattern,
subdividing the day into named English CLDR segments.
-/
inductive ExtendedDayPeriod

  /--
  Exactly 00:00:00
  -/
  | midnight

  /--
  21:00–06:00 (exclusive of midnight)
  -/
  | night

  /--
  06:00–12:00
  -/
  | morning

  /--
  Exactly 12:00:00
  -/
  | noon

  /--
  12:00–18:00
  -/
  | afternoon

  /--
  18:00–21:00
  -/
  | evening
  deriving Repr, Inhabited

/--
`Modifier` represents a single format pattern letter with its presentation style.

The table below lists every symbol, its `presentation` type, the `TypeFormat` value type produced
when parsing or consumed when formatting, and representative output examples.

```
Symbol  Meaning                        Presentation      TypeFormat                Examples
──────────────────────────────────────────────────────────────────────────────────────────────────
G       era                            Text              Year.Era                  AD; Anno Domini; A
u       year (proleptic/astronomical)  Year              Year.Offset               2004; 04; -0001; -1
y       year-of-era                    Year              Year.Offset               2004; 04; 0002; 2
D       day-of-year                    Number            Σ Day.Ordinal.OfYear      189
M/L     month-of-year                  Number ⊕ Text     Month.Ordinal             7; 07; Jul; July; J
d       day-of-month                   Number            Day.Ordinal               10
──────────────────────────────────────────────────────────────────────────────────────────────────
Q/q     quarter-of-year                Number ⊕ Text     Month.Quarter             3; 03; Q3; 3rd quarter
Y       week-based-year                Year              Year.Offset               1996; 96
w       week-of-week-based-year        Number            Week.Ordinal              27
W       week-of-month                  Number            Week.Ordinal.OfMonth      4
E       day-of-week (text only)        Text              Weekday                   Tue; Tuesday; T
e/c     localized day-of-week          Number ⊕ Text     Weekday                   2; 02; Tue; Tuesday; T
F       day-of-week-in-month           Number            Bounded.LE 1 5            3
──────────────────────────────────────────────────────────────────────────────────────────────────
a       am-pm-of-day                   Text              HourMarker                AM; PM
b       day-period (noon/midnight)     Text              DayPeriod                 AM; noon; midnight
B       extended day period            Text              ExtendedDayPeriod         in the morning; at night
h       clock-hour-of-am-pm (1-12)    Number            Bounded.LE 1 12           12
K       hour-of-am-pm (0-11)          Number            Bounded.LE 0 11           0
k       clock-hour-of-day (1-24)      Number            Bounded.LE 1 24           24
──────────────────────────────────────────────────────────────────────────────────────────────────
H       hour-of-day (0-23)            Number            Hour.Ordinal              0
m       minute-of-hour                Number            Minute.Ordinal            30
s       second-of-minute              Number            Second.Ordinal true       55
S       fraction-of-second            Fraction          Nanosecond.Ordinal        978
A       milli-of-day                  Number            Millisecond.Offset        1234
n       nano-of-second                Number            Nanosecond.Ordinal        987654321
N       nano-of-day                   Number            Nanosecond.Offset         1234000000
──────────────────────────────────────────────────────────────────────────────────────────────────
V       time-zone ID                  ZoneId            String                    America/Los_Angeles; Z
z       time-zone name                ZoneName          String                    Pacific Standard Time; PST
v       generic zone name             ZoneName          String                    Pacific Time; PT
O       localized zone-offset         OffsetO           Offset                    GMT+8; GMT+08:00
X       zone-offset ('Z' for zero)    OffsetX           Offset                    Z; -08; -0830; -08:30
x       zone-offset                   OffsetX           Offset                    +0000; -08; -0830; -08:30
Z       zone-offset                   OffsetZ           Offset                    +0000; -0800; -08:00
```
-/
inductive Modifier
  /--
  `G`: Era (e.g., AD, Anno Domini, A).
  -/
  | G (presentation : Text)

  /--
  `u`: Proleptic/astronomical year (e.g., 2004, 04, -0001, -1). Can be negative: year 0 exists and -0001 = 2 BC.
  Use `y` + `G` instead when you want the era-based (always-positive) representation.
  -/
  | u (presentation : Year)

  /--
  `y`: Year of era (e.g., 2004, 04, 0002, 2). Never negative: year 1 BC is formatted as `1` paired with a BC era
  designator. Use `u` instead when you need the proleptic/astronomical year (which can be negative).
  -/
  | y (presentation : Year)

  /--
  `D`: Day of year (e.g., 189).
  -/
  | D (presentation : Number)

  /--
  `M`: Month of year as number or text (e.g., 7, 07, Jul, July, J).
  -/
  | M (presentation : Number ⊕ Text)

  /--
  `L`: Stand-alone month of year as number or text (e.g., 7, 07, Jul, July, J).
  Stand-alone means the month is used independently (e.g., a calendar header "July") rather than as part of a full date.
  In practice the output is the same as `M`; the distinction is meaningful only in locale-aware contexts.
  -/
  | L (presentation : Number ⊕ Text)

  /--
  `d`: Day of month (e.g., 10).
  -/
  | d (presentation : Number)

  /--
  `Q`: Quarter of year as number or text (e.g., 3, 03, Q3, 3rd quarter).
  -/
  | Q (presentation : Number ⊕ Text)

  /--
  `q`: Stand-alone quarter of year as number or text (e.g., 3, 03, Q3, 3rd quarter).
  Stand-alone means the value is used independently (e.g., a calendar header) rather than as part of a full date phrase.
  In practice the output is the same as `Q`; the distinction is meaningful only in locale-aware contexts.
  -/
  | q (presentation : Number ⊕ Text)

  /--
  `Y`: ISO week-based year (e.g., 2004, 04, 0002, 2). This is the year that contains the ISO week (`w`), which can
  differ from the calendar year near year boundaries: e.g., Dec 31 may belong to week 1 of the following year.
  -/
  | Y (presentation : Year)

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
  `e`: Day of week as number or text (e.g., 1, 01, Mon, Monday, M).
  The numeric value uses Monday=1 through Sunday=7 (ISO 8601 convention).
  Text output is the same as `E`.
  -/
  | e (presentation : Number ⊕ Text)

  /--
  `c`: Stand-alone day of week as number or text (e.g., 2, Tue, Tuesday, T).
  Stand-alone means the day is used independently (e.g., a calendar column header) rather than as part of a full date.
  Unlike `e`, `cc` (count of 2) is not valid; the minimum is `c` (1 letter) or `ccc` (3 letters).
  -/
  | c (presentation : Number ⊕ Text)

  /--
  `F`: Day-of-week-in-month / occurrence of the weekday within the month (e.g., 2nd Sunday -> 2).
  -/
  | F (presentation : Number)

  /--
  `a`: AM/PM of day (e.g., PM).
  -/
  | a (presentation : Text)

  /--
  `b`: Day period with noon/midnight distinction (e.g., AM, noon, midnight).
  -/
  | b (presentation : Text)

  /--
  `B`: Extended day period with named segments (e.g., "in the morning", "at night").
  -/
  | B (presentation : Text)

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
  `V`: Time zone ID.
  - `V` (1 letter): outputs `"unk"` (unknown zone placeholder per Unicode CLDR).
  - `VV` (2 letters): outputs the IANA zone ID (e.g., `"America/Los_Angeles"`), or `"Z"` for UTC.
  -/
  | V (presentation : ZoneId)

  /--
  `z`: Time zone name (e.g., Pacific Standard Time, PST).
  -/
  | z (presentation : ZoneName)

  /--
  `v`: Generic time zone name, without DST distinction (e.g., Pacific Time, PT).
  -/
  | v (presentation : ZoneName)

  /--
  `O`: Localized zone offset using the `GMT` prefix (e.g., `GMT+8`, `GMT+08:00`).
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
  `Z`: Zone offset.
  - `Z`, `ZZ`, `ZZZ`: output `±HHMMss` (no colon); parse `±HHMM[ss]`. Does **not** accept the literal `Z` character for UTC — use `ZZZZZ` or `XXX` for that.
  - `ZZZZ`: outputs/parses localized GMT form (e.g., `GMT+08:00`).
  - `ZZZZZ`: outputs `±HH:mm[:ss]` and uses `Z` for UTC (e.g., `Z`, `+01:30`).
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
  | none => fail s!"invalid quantity of characters for '{p.front}'"

private def parseText (constructor : Text → Modifier) (p : String) : Parser Modifier :=
  parseMod constructor Text.classify p

private def classifyNumberMax (max : Nat) : Nat → Option Number
  | n => if n ≤ max then some ⟨n⟩ else none

private def classifySingleNumber : Nat → Option Number
  | 1 => some ⟨1⟩
  | _ => none

private def classifyWeekdayText : Nat → Option Text
  | 6 => some .twoLetterShort
  | n => Text.classify n

private def parseWeekdayText (constructor : Text → Modifier) (p : String) : Parser Modifier :=
  parseMod constructor classifyWeekdayText p

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
  match p.length with
  | 1 => pure (.V .unknown)
  | 2 => pure (.V .short)
  | _ => fail s!"invalid quantity of characters for '{p.front}': must be 1 or 2"

private def parseNumberText (constructor : (Number ⊕ Text) → Modifier) (p : String) : Parser Modifier :=
  parseMod constructor classifyNumberText p

private def classifyWeekdayNumberText : Nat → Option (Number ⊕ Text)
  | n =>
    if n < 3 then
      some (.inl ⟨n⟩)
    else if n = 6 then
      some (.inr .twoLetterShort)
    else
      .inr <$> Text.classify n

private def parseWeekdayNumberText (constructor : (Number ⊕ Text) → Modifier) (p : String) : Parser Modifier :=
  parseMod constructor classifyWeekdayNumberText p

private def classifyStandaloneWeekdayNumberText : Nat → Option (Number ⊕ Text)
  | 1 => some (.inl ⟨1⟩)
  | 6 => some (.inr .twoLetterShort)
  | n =>
    if n ≥ 3 then
      .inr <$> Text.classify n
    else
      none

private def parseStandaloneWeekdayNumberText (constructor : (Number ⊕ Text) → Modifier) (p : String) : Parser Modifier :=
  parseMod constructor classifyStandaloneWeekdayNumberText p

private def parseAMPM (p : String) : Parser Modifier :=
  parseText Modifier.a p

private def parseDayPeriod (p : String) : Parser Modifier :=
  parseText Modifier.b p

private def parseBPeriod (p : String) : Parser Modifier :=
  parseText Modifier.B p

private def parseZoneName (constructor : ZoneName → Modifier) (p : String) : Parser Modifier :=
  let len := p.length
  match ZoneName.classify (p.front) len with
  | some res => pure (constructor res)
  | none => fail s!"invalid quantity of characters for '{p.front}'"

/-- Parses a single format `Modifier` from the input string. -/
def parseModifier : Parser Modifier
  := (parseText Modifier.G =<< many1Chars (pchar 'G'))
  <|> parseYear Modifier.y =<< many1Chars (pchar 'y')
  <|> parseYear Modifier.Y =<< many1Chars (pchar 'Y')
  <|> parseYear Modifier.u =<< many1Chars (pchar 'u')
  <|> parseMod Modifier.D (classifyNumberMax 3) =<< many1Chars (pchar 'D')
  <|> parseNumberText Modifier.M =<< many1Chars (pchar 'M')
  <|> parseNumberText Modifier.L =<< many1Chars (pchar 'L')
  <|> parseMod Modifier.d (classifyNumberMax 2) =<< many1Chars (pchar 'd')
  <|> parseNumberText Modifier.Q =<< many1Chars (pchar 'Q')
  <|> parseNumberText Modifier.q =<< many1Chars (pchar 'q')
  <|> parseMod Modifier.w (classifyNumberMax 2) =<< many1Chars (pchar 'w')
  <|> parseMod Modifier.W classifySingleNumber =<< many1Chars (pchar 'W')
  <|> parseWeekdayText Modifier.E =<< many1Chars (pchar 'E')
  <|> parseWeekdayNumberText Modifier.e =<< many1Chars (pchar 'e')
  <|> parseStandaloneWeekdayNumberText Modifier.c =<< many1Chars (pchar 'c')
  <|> parseMod Modifier.F classifySingleNumber =<< many1Chars (pchar 'F')
  <|> parseAMPM =<< many1Chars (pchar 'a')
  <|> parseDayPeriod =<< many1Chars (pchar 'b')
  <|> parseBPeriod =<< many1Chars (pchar 'B')
  <|> parseMod Modifier.h (classifyNumberMax 2) =<< many1Chars (pchar 'h')
  <|> parseMod Modifier.K (classifyNumberMax 2) =<< many1Chars (pchar 'K')
  <|> parseMod Modifier.k (classifyNumberMax 2) =<< many1Chars (pchar 'k')
  <|> parseMod Modifier.H (classifyNumberMax 2) =<< many1Chars (pchar 'H')
  <|> parseMod Modifier.m (classifyNumberMax 2) =<< many1Chars (pchar 'm')
  <|> parseMod Modifier.s (classifyNumberMax 2) =<< many1Chars (pchar 's')
  <|> parseFraction Modifier.S =<< many1Chars (pchar 'S')
  <|> parseNumber Modifier.A =<< many1Chars (pchar 'A')
  <|> parseNumber Modifier.n =<< many1Chars (pchar 'n')
  <|> parseNumber Modifier.N =<< many1Chars (pchar 'N')
  <|> parseZoneId =<< many1Chars (pchar 'V')
  <|> parseZoneName Modifier.z =<< many1Chars (pchar 'z')
  <|> parseZoneName Modifier.v =<< many1Chars (pchar 'v')
  <|> parseOffsetO Modifier.O =<< many1Chars (pchar 'O')
  <|> parseOffsetX Modifier.X =<< many1Chars (pchar 'X')
  <|> parseOffsetX Modifier.x =<< many1Chars (pchar 'x')
  <|> parseOffsetZ Modifier.Z =<< many1Chars (pchar 'Z')

end Time
end Std
