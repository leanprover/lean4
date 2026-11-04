/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Time.Zoned
public import Std.Time.Format.Modifier
public import Std.Time.Format.DateFormat
import Init.Data.String.TakeDrop
import Init.Data.String.Search

public section

/-!
This module defines the `Formatter` types. It is based on the Java's `DateTimeFormatter` format.
-/

namespace Std
namespace Time
open Std.Time.Internal
open Std.Internal.Parsec.String
open Std.Internal.Parsec Lean PlainTime PlainDate TimeZone DateTime

set_option linter.all true

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

  /--
  Locale configuration for formatting and parsing, including locale-specific symbols and the first
  day of the week used for week-of-year and week-of-month calculations.
  Default is `DateFormat.enUS` (English, US).
  -/
  dateformat : DateFormat := DateFormat.enUS
deriving Inhabited

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
deriving Inhabited

private def parseFormatPart : Parser FormatPart
  := (.modifier <$> parseModifier)
  <|> (pchar '\\') *> any <&> (.string ∘ toString)
  <|> (pchar '\"' *>  many1Chars (satisfy (· ≠ '\"')) <* pchar '\"') <&> .string
  <|> (pchar '\'' *>  many1Chars (satisfy (· ≠ '\'')) <* pchar '\'') <&> .string
  <|> many1Chars (satisfy (fun x => ¬Char.isAlpha x ∧ x ≠ '\'' ∧ x ≠ '\"')) <&> .string

private def specParser : Parser FormatString :=
  (Array.toList <$> many parseFormatPart) <* eof

-- Pretty printer

private def leftPadAscii (n : Nat) (a : Char) (s : String) : String :=
  "".pushn a (n -  s.positions.length) ++ s

private def rightPadAscii (n : Nat) (a : Char) (s : String) : String :=
  s ++ "".pushn a (n - s.positions.length)

private def pad (size : Nat) (n : Int) (cut : Bool := false) : String :=
  let (sign, n) := if n < 0 then ("-", -n) else ("", n)

  let numStr := toString n
  if numStr.utf8ByteSize > size then
    sign ++ if cut then numStr.drop (numStr.utf8ByteSize - size) |>.copy else numStr
  else
    sign ++ leftPadAscii size '0' numStr

/--
A four-letter year field. A year that needs more than four digits gets an explicit sign, which tells
the parser to read past four digits.
-/
private def padFourDigitYear (n : Int) : String :=
  if n > 9999 then "+" ++ toString n else pad 4 n

private def monthNames (symbols : DateFormatSymbols) : Text → Vector String 12
  | .short | .twoLetterShort => symbols.monthShort
  | .full => symbols.monthLong
  | .narrow => symbols.monthNarrow

private def weekdayNames (symbols : DateFormatSymbols) : Text → Vector String 7
  | .short => symbols.weekdayShort
  | .full => symbols.weekdayLong
  | .narrow => symbols.weekdayNarrow
  | .twoLetterShort => symbols.weekdayTwoLetter

private def eraNames (symbols : DateFormatSymbols) : Text → Vector String 2
  | .short | .twoLetterShort => symbols.eraShort
  | .full => symbols.eraLong
  | .narrow => symbols.eraNarrow

private def quarterNames (symbols : DateFormatSymbols) : Text → Vector String 4
  | .short => symbols.quarterShort
  | .full => symbols.quarterLong
  | .narrow | .twoLetterShort => symbols.quarterNarrow

/-- AM, then PM. -/
private def markerNames (symbols : DateFormatSymbols) : Text → Vector String 2
  | .short | .twoLetterShort => ⟨#[symbols.amShort, symbols.pmShort], rfl⟩
  | .full => ⟨#[symbols.amLong, symbols.pmLong], rfl⟩
  | .narrow => ⟨#[symbols.amNarrow, symbols.pmNarrow], rfl⟩

/-- Midnight, noon, AM and PM, in the order that parsing tries them. -/
private def dayPeriodNames (symbols : DateFormatSymbols) (text : Text) : Vector String 4 :=
  let names := match text with
    | .short | .twoLetterShort => symbols.dayPeriodShort
    | .full => symbols.dayPeriodLong
    | .narrow => symbols.dayPeriodNarrow
  ⟨#[names.midnight, names.noon, names.am, names.pm], rfl⟩

private def extendedDayPeriodNames (symbols : DateFormatSymbols) : Text → Vector String 6
  | .short | .twoLetterShort => symbols.extendedDayPeriodShort
  | .full => symbols.extendedDayPeriodLong
  | .narrow => symbols.extendedDayPeriodNarrow

private def monthIndex (month : Month.Ordinal) : Fin 12 :=
  month.sub 1 |>.toFin (by decide)

private def monthOfIndex (i : Fin 12) : Month.Ordinal :=
  Bounded.LE.ofFin i |>.add 1

private def weekdayIndex (weekday : Weekday) : Fin 7 :=
  weekday.toOrdinal.sub 1 |>.toFin (by decide)

private def weekdayOfIndex (i : Fin 7) : Weekday :=
  .ofOrdinal (Bounded.LE.ofFin i |>.add 1)

private def eraIndex : Year.Era → Fin 2
  | .bce => 0
  | .ce => 1

private def eraOfIndex (i : Fin 2) : Year.Era :=
  if i = 0 then .bce else .ce

private def quarterIndex (quarter : Month.Quarter) : Fin 4 :=
  quarter.sub 1 |>.toFin (by decide)

private def quarterOfIndex (i : Fin 4) : Month.Quarter :=
  Bounded.LE.ofFin i |>.add 1

private def markerIndex : HourMarker → Fin 2
  | .am => 0
  | .pm => 1

private def markerOfIndex (i : Fin 2) : HourMarker :=
  if i = 0 then .am else .pm

private def dayPeriodIndex : DayPeriod → Fin 4
  | .midnight => 0
  | .noon => 1
  | .am => 2
  | .pm => 3

private def dayPeriodOfIndex : Fin 4 → DayPeriod
  | 0 => .midnight
  | 1 => .noon
  | 2 => .am
  | _ => .pm

private def extendedDayPeriodIndex : ExtendedDayPeriod → Fin 6
  | .midnight  => 0
  | .night     => 1
  | .morning   => 2
  | .noon      => 3
  | .afternoon => 4
  | .evening   => 5

private def extendedDayPeriodOfIndex : Fin 6 → ExtendedDayPeriod
  | 0 => .midnight
  | 1 => .night
  | 2 => .morning
  | 3 => .noon
  | 4 => .afternoon
  | _ => .evening

/-- `offset` without its seconds, keeping its sign. -/
private def dropSeconds (offset : Offset) : Offset :=
  .ofSeconds (.ofInt (offset.second.val.tdiv 60 * 60))

/-- The `x` forms of an offset. `X` writes the same, except `Z` for UTC. -/
private def formatOffsetX (offset : Offset) : OffsetX → String
  | .hour =>
    let hourMinute := (dropSeconds offset).toIsoString false
    if offset.second.val.natAbs / 60 % 60 = 0 then (hourMinute.dropEnd 2).copy else hourMinute
  | .hourMinute => (dropSeconds offset).toIsoString false
  | .hourMinuteColon => (dropSeconds offset).toIsoString true
  | .hourMinuteSecond => offset.toIsoString false
  | .hourMinuteSecondColon => offset.toIsoString true

/-- `GMT` followed by the offset, or a bare `GMT` for UTC. -/
private def formatGmtOffset (offset : Offset) : String :=
  if offset.second.val = 0 then "GMT" else s!"GMT{offset.toIsoString true}"

/-- A zone name or abbreviation. An offset-only zone, whose label is its offset, shows it after `GMT`. -/
private def zoneLabel (label : String) (offset : Offset) : String :=
  if label.startsWith "+" || label.startsWith "-" then s!"GMT{offset.toIsoString true}" else label

/-- Classify a `PlainTime` into a `DayPeriod` for the `b` pattern. -/
def classifyDayPeriod (hour : Hour.Ordinal) (minute : Minute.Ordinal) (second : Second.Ordinal true) : DayPeriod :=
  if hour.val = 0 ∧ minute.val = 0 ∧ second.val = 0 then .midnight
  else if hour.val = 12 ∧ minute.val = 0 ∧ second.val = 0 then .noon
  else if hour.val < 12 then .am
  else .pm

/-- Classify a `PlainTime` into an `ExtendedDayPeriod` for the `B` pattern (CLDR flexible periods). -/
def classifyExtendedDayPeriod (hour : Hour.Ordinal) (minute : Minute.Ordinal) (second : Second.Ordinal true) : ExtendedDayPeriod :=
  if hour.val = 0 ∧ minute.val = 0 ∧ second.val = 0 then .midnight
  else if hour.val = 12 ∧ minute.val = 0 ∧ second.val = 0 then .noon
  else if hour.val < 6 then .night
  else if hour.val < 12 then .morning
  else if hour.val < 18 then .afternoon
  else if hour.val < 21 then .evening
  else .night

set_option linter.missingDocs false in  -- TODO
@[expose /- for codegen -/]
def TypeFormat : Modifier → Type
  | .G _  => Year.Era
  | .y _  => Year.Offset
  | .u _  => Year.Offset
  | .Y _  => Year.Offset
  | .D _  => Sigma Day.Ordinal.OfYear
  | .M _  => Month.Ordinal
  | .L _  => Month.Ordinal
  | .d _  => Day.Ordinal
  | .Q _  => Month.Quarter
  | .q _  => Month.Quarter
  | .w _  => Week.OfYear.Ordinal
  | .W _  => Week.Ordinal
  | .E _  => Weekday
  | .e _  => Weekday
  | .c _  => Weekday
  | .F _  => Week.Aligned.Ordinal
  | .a _  => HourMarker
  | .b _  => DayPeriod
  | .B _  => ExtendedDayPeriod
  | .h _  => Bounded.LE 1 12
  | .K _  => Bounded.LE 0 11
  | .k _  => Bounded.LE 1 24
  | .H _  => Hour.Ordinal
  | .m _  => Minute.Ordinal
  | .s _  => Second.Ordinal true
  | .S _  => Nanosecond.Ordinal
  | .A _  => Millisecond.Offset
  | .n _  => Nanosecond.Ordinal
  | .N _  => Nanosecond.Offset
  | .V _  => String
  | .z _  => String
  | .v _  => String
  | .O _  => Offset
  | .X _  => Offset
  | .x _  => Offset
  | .Z _  => Offset

private def formatWith (dateformat : DateFormat) (modifier : Modifier) (data : TypeFormat modifier) : String :=
  match modifier with
  | .G text => (eraNames dateformat.symbols text).get (eraIndex data)
  | .y format =>
    let info := data.toInt
    let info := if info ≤ 0 then -info + 1 else info
    match format with
    | .any      => pad 0 info
    | .twoDigit => pad 2 (info % 100)
    | .fourDigit => padFourDigitYear info
    | .extended n => pad n info
  | .u format | .Y format =>
    match format with
    | .any      => pad 0 (data.toInt)
    | .twoDigit => pad 2 (data.toInt % 100)
    | .fourDigit => padFourDigitYear data.toInt
    | .extended n => pad n data.toInt
  | .D format =>
    pad format.padding data.snd.val
  | .M format | .L format =>
    match format with
    | .inl fmt  => pad fmt.padding data.val
    | .inr text => (monthNames dateformat.symbols text).get (monthIndex data)
  | .d format =>
    pad format.padding data.val
  | .Q format | .q format =>
    match format with
    | .inl fmt  => pad fmt.padding data.val
    | .inr text => (quarterNames dateformat.symbols text).get (quarterIndex data)
  | .w format =>
    pad format.padding data.val
  | .W format =>
    pad format.padding data.val
  | .E text => (weekdayNames dateformat.symbols text).get (weekdayIndex data)
  | .e format | .c format =>
    match format with
    | .inl fmt =>
      let firstOrd : Int := dateformat.firstDayOfWeek.toOrdinal.val
      let dayOrd : Int := data.toOrdinal.val
      pad fmt.padding ((dayOrd - firstOrd + 7) % 7 + 1)
    | .inr text => (weekdayNames dateformat.symbols text).get (weekdayIndex data)
  | .F format =>
    pad format.padding data.val
  | .a text => (markerNames dateformat.symbols text).get (markerIndex data)
  | .b text => (dayPeriodNames dateformat.symbols text).get (dayPeriodIndex data)
  | .B text => (extendedDayPeriodNames dateformat.symbols text).get (extendedDayPeriodIndex data)
  | .h format => pad format.padding data.val
  | .K format => pad format.padding data.val
  | .k format => pad format.padding data.val
  | .H format => pad format.padding data.val
  | .m format => pad format.padding data.val
  | .s format => pad format.padding data.val
  | .S format =>
    match format with
    | .nano      => pad 9 data.val
    | .truncated n =>
      -- Pad to 9 digits first so truncation is from the left of the full nanosecond string
      let s := leftPadAscii 9 '0' (toString data.val)
      (s.take n).toString
  | .A format =>
    pad format.padding data.val
  | .n format =>
    pad format.padding data.val
  | .N format =>
    pad format.padding data.val
  | .V .unknown => "unk"
  | .V _ | .z _ | .v _ => data
  | .O .short =>
    if data.second == 0 then "GMT"
    else
      let (sign, time) := if data.second.val ≥ 0 then ("+", data.second) else ("-", -data.second)
      let t := PlainTime.ofSeconds time
      let pad := leftPadAscii 2 '0' ∘ toString
      if t.second.val != 0 then s!"GMT{sign}{t.hour.val}:{pad t.minute.val}:{pad t.second.val}"
      else if t.minute.val == 0 then s!"GMT{sign}{t.hour.val}"
      else s!"GMT{sign}{t.hour.val}:{pad t.minute.val}"
  | .O .full | .Z .full => formatGmtOffset data
  | .X format => if data.second.val = 0 then "Z" else formatOffsetX data format
  | .x format => formatOffsetX data format
  | .Z .hourMinute => data.toIsoString false
  | .Z .hourMinuteSecondColon => if data.second.val = 0 then "Z" else data.toIsoString true

/--
The value that `modifier` shows for a date, a time of day and a zone, or `none` when the modifier
needs one of them and it is missing.
-/
private def fieldValue? (dateformat : DateFormat) (date? : Option PlainDate) (time? : Option PlainTime)
    (zone? : Option TimeZone) (modifier : Modifier) : Option (TypeFormat modifier) :=
  let firstDay := dateformat.firstDayOfWeek
  let minDays := dateformat.minimalDaysInFirstWeek
  match modifier with
  | .G _ => date?.map (·.era)
  | .y _ | .u _ => date?.map (·.year)
  | .Y _ => date?.map (·.weekYear firstDay minDays)
  | .D _ => date?.map fun date => ⟨_, date.dayOfYear⟩
  | .M _ | .L _ => date?.map (·.month)
  | .d _ => date?.map (·.day)
  | .Q _ | .q _ => date?.map (·.quarter)
  | .w _ => date?.map (·.weekOfYear firstDay minDays)
  | .W _ => date?.map (·.weekOfMonth firstDay)
  | .E _ | .e _ | .c _ => date?.map (·.weekday)
  | .F _ => date?.map (·.alignedWeekOfMonth)
  | .a _ => time?.map (HourMarker.ofOrdinal ·.hour)
  | .b _ => time?.map fun time => classifyDayPeriod time.hour time.minute time.second
  | .B _ => time?.map fun time => classifyExtendedDayPeriod time.hour time.minute time.second
  | .h _ => time?.map (·.hour.toRelative)
  | .K _ => time?.map (·.hour.emod 12 (by decide))
  | .k _ => time?.map (·.hour.shiftTo1BasedHour)
  | .H _ => time?.map (·.hour)
  | .m _ => time?.map (·.minute)
  | .s _ => time?.map (·.second)
  | .S _ | .n _ => time?.map (·.nanosecond)
  | .A _ => time?.map (·.toMilliseconds)
  | .N _ => time?.map (·.toNanoseconds)
  | .V .unknown => zone?.map fun _ => "unk"
  | .V _ | .z .full | .v .full => zone?.map fun tz => zoneLabel tz.name tz.offset
  | .z .short | .v .short => zone?.map fun tz => zoneLabel tz.abbreviation tz.offset
  | .O _ | .X _ | .x _ | .Z _ => zone?.map (·.offset)

private def parseFromSymbols {α : Type} (pairs : Array (String × α)) : Parser α :=
  pairs.foldl (fun acc (s, v) => acc <|> pstring s *> pure v) (fail "no match")

/-- One of `names`, tried in order, as its index. -/
private def parseName (names : Vector String n) : Parser (Fin n) :=
  parseFromSymbols (names.mapFinIdx fun i name h => (name, (⟨i, h⟩ : Fin n))).toArray

/--
Parses a short month name using the given locale symbols and returns the corresponding `Month.Ordinal`.
-/
def parseMonthShort (symbols : DateFormatSymbols) : Parser Month.Ordinal :=
  monthOfIndex <$> parseName symbols.monthShort

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

/-- The length of the run of digits at the current position, without consuming it. -/
private def digitRunLength : Parser Nat := fun it =>
  match manyChars (satisfy Char.isDigit) it with
  | .success _ run => .success it run.length
  | .error _ err => .error it err

/--
A number of at least `width` digits. `reserve` is the count of digits that the numeric fields right
after it need, and it reads the run of digits except those, so that patterns such as `uMMdd` can
split the digits. With `reserve = none` those fields vary in width, and it reads exactly `width`
digits, or every digit when `width` is 1.
-/
private def parseVarWidthNum (width : Nat) (reserve : Option Nat) : Parser Nat :=
  match reserve with
  | none => parseFlexibleNum width
  | some r => do parseNum (max width ((← digitRunLength) - r))

/-- A four-letter year field: four digits, or more after the sign that `padFourDigitYear` writes. -/
private def parseFourDigitYear (negative : Bool) (reserve : Option Nat) : Parser Int := do
  let minus : Parser Int := if negative then pchar '-' *> pure (-1) else fail "expected: +"
  let sign ← optional ((pchar '+' *> pure 1) <|> minus)
  let digits ← if sign.isSome then parseVarWidthNum 4 reserve else parseNum 4
  return sign.getD 1 * digits

private def parseFractionNum (size : Nat) (pad : Nat) : Parser Nat :=
  String.toNat! <$> rightPadAscii pad '0' <$> exactlyChars (satisfy Char.isDigit) size

private def parseIdentifier : Parser String :=
  many1Chars (satisfy (fun x => x.isAlpha ∨ x.isDigit ∨ x = '_' ∨ x = '-' ∨ x = '+' ∨ x = '/' ∨ x = ':'))

/-- A zone id or name. `TimeZone.GMT`'s name has spaces, so it is matched whole. -/
private def parseZoneId : Parser String :=
  pstring TimeZone.GMT.name <|> parseIdentifier

private def parseNatToBounded { n m : Nat } (parser : Parser Nat) : Parser (Bounded.LE n m) := do
  let res ← parser
  if h : n ≤ res ∧ res ≤ m then
    return Bounded.LE.ofNat' res h
  else
    fail s!"need a natural number in the interval of {n} to {m}"

private def parseOneOrTwoNum : Parser Nat := do
  let first ← satisfy Char.isDigit
  match ← optional (satisfy Char.isDigit) with
  | some res => return (first.toNat - 48) * 10 + (res.toNat - 48)
  | none => return (first.toNat - 48)

/-- Whether an offset component is written: always, never, or only when it is non-zero. -/
private inductive Reason
  | yes
  | no
  | optional

private def parseOffset (withMinutes : Reason) (withSeconds : Reason) (withColon : Bool) : Parser Offset := do
  let sign ← (pchar '+' *> pure 1) <|> (pchar '-' *> pure (-1))
  let hours : Hour.Offset ← UnitVal.ofInt <$> parseOneOrTwoNum

  if hours.val < 0 ∨ hours.val > 23 then
    fail s!"invalid hour offset: {hours.val}. Must be between 0 and 23."

  let colon := if withColon then pchar ':' else pure ':'

  let parseUnit {n} (reason : Reason) : Parser (Option (UnitVal n)) :=
    match reason with
    | .yes => some <$> (colon *> UnitVal.ofInt <$> parseOneOrTwoNum)
    | .no => pure none
    | .optional => optional (colon *> UnitVal.ofInt <$> parseOneOrTwoNum)

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

/-- The `x` forms of an offset. `X` reads the same, and also `Z` for UTC. -/
private def parseOffsetX : OffsetX → Parser Offset
  | .hour => parseOffset .optional .no false
  | .hourMinute => parseOffset .yes .no false
  | .hourMinuteColon => parseOffset .yes .optional true
  | .hourMinuteSecond => parseOffset .yes .optional false
  | .hourMinuteSecondColon => parseOffset .yes .optional true

/-- `GMT`, optionally followed by an offset whose minutes are `minutes`. -/
private def parseGmtOffset (minutes : Reason) : Parser Offset := do
  skipString "GMT"
  return (← optional (parseOffset minutes .optional true)).getD Offset.zero

/-- Whether a field is written as digits, which a number right before it must leave to it. -/
private def isNumericModifier : Modifier → Bool
  | .y _ | .u _ | .Y _ | .D _ | .d _ | .w _ | .W _ | .F _ | .h _ | .K _ | .k _ | .H _ | .m _ | .s _
  | .S _ | .A _ | .n _ | .N _ => true
  | .M (.inl _) | .L (.inl _) | .Q (.inl _) | .q (.inl _) | .e (.inl _) | .c (.inl _) => true
  | _ => false

/--
The digits a numeric field always takes: its letter count, once that covers the field's largest
value. A field that can take more digits has no fixed width.
-/
private def fixedDigits : Modifier → Option Nat
  | .y .twoDigit | .u .twoDigit | .Y .twoDigit => some 2
  | .y .fourDigit | .u .fourDigit | .Y .fourDigit => some 4
  | .S .nano => some 9
  | .S (.truncated n) => some n
  | .Q (.inl p) | .q (.inl p) | .e (.inl p) | .c (.inl p) | .W p | .F p => covering 1 p
  | .d p | .w p | .h p | .K p | .k p | .H p | .m p | .s p | .M (.inl p) | .L (.inl p) => covering 2 p
  | .D p => covering 3 p
  | .A p => covering 8 p
  | .n p => covering 9 p
  | .N p => covering 14 p
  | _ => none
where
  covering (digits : Nat) (p : Number) : Option Nat :=
    if p.padding ≥ digits then some p.padding else none

/-- A numeric field: exactly its fixed width, or else at least `width` digits (see `parseVarWidthNum`). -/
private def parseField (m : Modifier) (width : Nat) (reserve : Option Nat) : Parser Nat :=
  match fixedDigits m with
  | some fixed => parseNum fixed
  | none => parseVarWidthNum width reserve

/--
The digits that the numeric fields at the start of `rest` need: `some 0` when `rest` does not start
with a numeric field, and `none` when one of those fields varies in width.
-/
private def reservedDigits : FormatString → Option Nat
  | .modifier m :: rest =>
    if isNumericModifier m then (· + ·) <$> fixedDigits m <*> reservedDigits rest else some 0
  | _ => some 0

/-- `reserve`: the `reservedDigits` of the rest of the format. -/
private def parseWith (config : FormatConfig) (reserve : Option Nat) : (mod : Modifier) → Parser (TypeFormat mod)
  | .G text => eraOfIndex <$> parseName (eraNames config.dateformat.symbols text)
  | .y format =>
    match format with
    | .any => Int.ofNat <$> parseVarWidthNum 1 reserve
    | .twoDigit => (2000 + ·) <$> Int.ofNat <$> parseNum 2
    | .fourDigit => parseFourDigitYear false reserve
    | .extended n => Int.ofNat <$> parseVarWidthNum n reserve
  | .u format | .Y format =>
    match format with
    | .any => parseSigned <| parseVarWidthNum 1 reserve
    | .twoDigit => (2000 + ·) <$> Int.ofNat <$> parseNum 2
    | .fourDigit => parseFourDigitYear true reserve
    | .extended n => parseSigned <| parseVarWidthNum n reserve
  | .D format => Sigma.mk true <$> parseNatToBounded (parseField (.D format) format.padding reserve)
  | .M format | .L format =>
    match format with
    | .inl fmt  => parseNatToBounded (parseField (.M (.inl fmt)) fmt.padding reserve)
    | .inr text => monthOfIndex <$> parseName (monthNames config.dateformat.symbols text)
  | .d format => parseNatToBounded (parseField (.d format) format.padding reserve)
  | .Q format | .q format =>
    match format with
    | .inl fmt  => parseNatToBounded (parseField (.Q (.inl fmt)) fmt.padding reserve)
    | .inr text => quarterOfIndex <$> parseName (quarterNames config.dateformat.symbols text)
  | .w format => parseNatToBounded (parseField (.w format) format.padding reserve)
  | .W format => parseNatToBounded (parseField (.W format) format.padding reserve)
  | .E text => weekdayOfIndex <$> parseName (weekdayNames config.dateformat.symbols text)
  | .e format | .c format =>
    match format with
    | .inl fmt => do
      let n ← parseField (.e (.inl fmt)) fmt.padding reserve
      if ¬ (1 ≤ n ∧ n ≤ 7) then fail "need a natural number in the interval of 1 to 7"
      let firstOrd : Int := config.dateformat.firstDayOfWeek.toOrdinal.val
      let absOrd : Int := ((n : Int) - 1 + firstOrd - 1) % 7 + 1
      return Weekday.ofOrdinal (Bounded.LE.ofNatWrapping absOrd (by decide))
    | .inr text => weekdayOfIndex <$> parseName (weekdayNames config.dateformat.symbols text)
  | .F format => parseNatToBounded (parseField (.F format) format.padding reserve)
  | .a text => markerOfIndex <$> parseName (markerNames config.dateformat.symbols text)
  | .b text => dayPeriodOfIndex <$> parseName (dayPeriodNames config.dateformat.symbols text)
  | .B text => extendedDayPeriodOfIndex <$> parseName (extendedDayPeriodNames config.dateformat.symbols text)
  | .h format => parseNatToBounded (parseField (.h format) format.padding reserve)
  | .K format => parseNatToBounded (parseField (.K format) format.padding reserve)
  | .k format => parseNatToBounded (parseField (.k format) format.padding reserve)
  | .H format => parseNatToBounded (parseField (.H format) format.padding reserve)
  | .m format => parseNatToBounded (parseField (.m format) format.padding reserve)
  | .s format =>
    if config.allowLeapSeconds then
      parseNatToBounded (parseField (.s format) format.padding reserve)
    else do
      let res : Bounded.LE 0 59 ← parseNatToBounded (parseField (.s format) format.padding reserve)
      return res.expandTop (by decide)
  | .S format =>
    match format with
    | .nano => parseNatToBounded (parseFlexibleNum 9)
    | .truncated n => parseNatToBounded (parseFractionNum n 9)
  | .A format => Millisecond.Offset.ofNat <$> parseField (.A format) format.padding reserve
  | .n format => parseNatToBounded (parseField (.n format) format.padding reserve)
  | .N format => Nanosecond.Offset.ofNat <$> parseField (.N format) format.padding reserve
  | .V format =>
    match format with
    | .unknown => pstring "unk" *> pure "unk"
    | .short | .full => parseZoneId
  | .z format =>
    match format with
    | .short | .full => parseZoneId
  | .v format =>
    match format with
    | .short | .full => parseZoneId
  | .O .short => parseGmtOffset .optional
  | .O .full | .Z .full => parseGmtOffset .yes
  | .X format => parseOffsetX format <|> (pstring "Z" *> pure Offset.zero)
  | .x format => parseOffsetX format
  | .Z .hourMinute => parseOffset .yes .optional false
  | .Z .hourMinuteSecondColon => (skipString "Z" *> pure Offset.zero) <|> parseOffset .yes .optional true

set_option linter.missingDocs false in  -- TODO
@[simp, expose /- for codegen -/]
def FormatType (result : Type) : FormatString → Type
  | .modifier entry :: xs => (TypeFormat entry) → (FormatType result xs)
  | .string _ :: xs => (FormatType result xs)
  | [] => result

namespace GenericFormat

private structure DateBuilder where
  G : Option Year.Era := none
  y : Option Year.Offset := none
  u : Option Year.Offset := none
  Y : Option Year.Offset := none
  D : Option (Sigma Day.Ordinal.OfYear) := none
  M : Option Month.Ordinal := none
  L : Option Month.Ordinal := none
  d : Option Day.Ordinal := none
  Q : Option Month.Quarter := none
  q : Option Month.Quarter := none
  w : Option Week.OfYear.Ordinal := none
  W : Option Week.Ordinal := none
  E : Option Weekday := none
  e : Option Weekday := none
  c : Option Weekday := none
  F : Option (Bounded.LE 1 5) := none
  a : Option HourMarker := none
  b : Option DayPeriod := none
  B : Option ExtendedDayPeriod := none
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
  v : Option String := none
  O : Option Offset := none
  X : Option Offset := none
  x : Option Offset := none
  Z : Option Offset := none

namespace DateBuilder

private def insert (date : DateBuilder) (modifier : Modifier) (data : TypeFormat modifier) : DateBuilder :=
  match modifier with
  | .G _  => { date with G := some data }
  | .y _  => { date with y := some data }
  | .u _  => { date with u := some data }
  | .Y _  => { date with Y := some data }
  | .D _  => { date with D := some data }
  | .M _  => { date with M := some data }
  | .L _  => { date with L := some data }
  | .d _  => { date with d := some data }
  | .Q _  => { date with Q := some data }
  | .q _  => { date with q := some data }
  | .w _  => { date with w := some data }
  | .W _  => { date with W := some data }
  | .E _  => { date with E := some data }
  | .e _  => { date with e := some data }
  | .c _  => { date with c := some data }
  | .F _  => { date with F := some data }
  | .a _  => { date with a := some data }
  | .b _  => { date with b := some data }
  | .B _  => { date with B := some data }
  | .h _  => { date with h := some data }
  | .K _  => { date with K := some data }
  | .k _  => { date with k := some data }
  | .H _  => { date with H := some data }
  | .m _  => { date with m := some data }
  | .s _  => { date with s := some data }
  | .S _  => { date with S := some data }
  | .A _  => { date with A := some data }
  | .n _  => { date with n := some data }
  | .N _  => { date with N := some data }
  | .V .full => { date with V := some data }
  | .V .short => { date with V := some data }
  | .V .unknown => { date with V := some data }
  | .z .full => { date with z := some data }
  | .z .short => { date with zabbrev := some data }
  | .v .full => { date with v := some data }
  | .v .short => { date with zabbrev := some data }
  | .O _  => { date with O := some data }
  | .X _  => { date with X := some data }
  | .x _  => { date with x := some data }
  | .Z _  => { date with Z := some data }

private def convertYearAndEra (year : Year.Offset) : Year.Era → Year.Offset
  | .ce => year
  | .bce => 1 - year

/-- Infer an `HourMarker` from a `DayPeriod` parsed by `b`. -/
private def markerOfDayPeriod : DayPeriod → HourMarker
  | .am | .midnight => .am
  | .pm | .noon     => .pm

/--
Infer an `HourMarker` from an `ExtendedDayPeriod` parsed by `B` and the hour on the 0–11 clock.
`.night` spans midnight (21:00–05:59), so the hour decides its marker.
-/
private def markerOfExtendedDayPeriod (hour : Int) : ExtendedDayPeriod → HourMarker
  | .midnight | .morning => .am
  | .noon | .afternoon | .evening => .pm
  | .night => if hour < 6 then .am else .pm

/--
The offset of a `±hh:mm[:ss]` or `GMT±hh:mm[:ss]` zone id: the name of an offset-only zone and the
form `V`, `z` and `v` write for it.
-/
private def offsetOfZoneId? (id : String) : Option Offset :=
  (optional (skipString "GMT") *> parseOffset .yes .optional true <* eof).run id |>.toOption

/--
The date in week `week` of the week-based year `year`, on `weekday`. Fails when that week does not
belong to `year`, such as week 53 of a year with 52 weeks.
-/
private def ofWeekDate (dateformat : DateFormat) (year : Year.Offset) (week : Week.OfYear.Ordinal) (weekday : Weekday) : Option PlainDate :=
  let firstDay := dateformat.firstDayOfWeek
  let minDays := dateformat.minimalDaysInFirstWeek
  let start := PlainDate.startOfWeekBasedYear year firstDay minDays
  let dayOfWeek := (weekday.toOrdinal.val - firstDay.toOrdinal.val) % 7
  let date := start.addDays (Day.Offset.ofInt ((week.val - 1) * 7 + dayOfWeek))
  if date.weekYear firstDay minDays == year then some date else none

/--
The date with `month` and `day` whose week-based year is `year`. Near January 1st two dates can
qualify, and the one in calendar year `year` wins.
-/
private def ofWeekYearMonthDay (dateformat : DateFormat) (year : Year.Offset) (month : Month.Ordinal) (day : Day.Ordinal) : Option PlainDate :=
  [year, year - 1, year + 1].findSome? fun calendarYear => do
    let date ← PlainDate.ofYearMonthDay? calendarYear month day
    guard (date.weekYear dateformat.firstDayOfWeek dateformat.minimalDaysInFirstWeek == year)
    return date

private def build (builder : DateBuilder) (aw : Awareness) (dateformat : DateFormat) : Option DateTime :=
  let offset :=
    builder.O <|> builder.X <|> builder.x <|> builder.Z
    <|> ((builder.V <|> builder.v <|> builder.z <|> builder.zabbrev) >>= offsetOfZoneId?)
    |>.getD Offset.zero

  let tz : TimeZone := {
    offset,
    name := builder.V <|> builder.v <|> builder.z |>.getD (offset.toIsoString true),
    abbreviation := builder.zabbrev |>.getD (offset.toIsoString true),
    isDST := false,
  }

  let calendarYear := builder.u <|> ((convertYearAndEra · (builder.G.getD .ce)) <$> builder.y)
  let month? := builder.M <|> builder.L

  -- Without `u` or `y`, a week-based year `Y` places a month and day, or else the week fields.
  let date : Option PlainDate :=
    if month?.isSome ∨ builder.d.isSome then
      let month := month?.getD 1
      let day := builder.d.getD 1
      match calendarYear, builder.Y with
      | none, some basedYear => ofWeekYearMonthDay dateformat basedYear month day
      | year?, _ => PlainDate.ofYearMonthDay? (year?.getD 0) month day
    else if let some ⟨_, ordinal⟩ := builder.D then
      let year := calendarYear.getD 0
      PlainDate.ofYearOrdinal year <$> Bounded.ofInt? ordinal.val
    else
      match calendarYear, builder.Y with
      | none, some basedYear =>
        let weekday := builder.e <|> builder.c <|> builder.E |>.getD dateformat.firstDayOfWeek
        ofWeekDate dateformat basedYear (builder.w.getD 1) weekday
      | year?, _ => PlainDate.ofYearMonthDay? (year?.getD 0) 1 1

  let halfDayHour : Option Int := ((·.val % 12) <$> builder.h) <|> ((·.val) <$> builder.K)

  -- Derive hour marker from `a`, then fall back to `b` and `B`.
  let markerOpt : Option HourMarker :=
    builder.a
    <|> (markerOfDayPeriod <$> builder.b)
    <|> (markerOfExtendedDayPeriod (halfDayHour.getD 0) <$> builder.B)

  let ofHalfDay (marker : HourMarker) : Option (Bounded.LE 0 23) :=
    let ofK (k : Bounded.LE 0 11) : Bounded.LE 0 23 :=
      match marker with
      | .am => k.expandTop (by decide)
      | .pm => (k.add 12).expandBottom (by decide)
    let ofh : Option (Bounded.LE 0 23) := marker.toAbsolute <$> builder.h
    ofh <|> ofK <$> builder.K

  let ofH : Option (Bounded.LE 0 23) := builder.H
  let ofk : Option (Bounded.LE 0 23) := (·.emod 24 (by decide)) <$> builder.k
  let ofDay := ofH <|> ofk

  -- Without a marker, `h` and `K` are read as AM hours.
  let hour := markerOpt.bind ofHalfDay <|> ofDay <|> ofHalfDay .am |>.getD ⟨0, by decide⟩

  let minute := builder.m |>.getD 0
  let second := builder.s |>.getD 0
  let nano := (builder.n <|> builder.S) |>.getD 0

  let time
    :=  PlainTime.ofNanoseconds <$> builder.N
    <|> PlainTime.ofMilliseconds <$> builder.A
    |>.getD (PlainTime.mk hour minute second nano)

  let datetime : Option PlainDateTime := date.map ({ date := ·, time })

  let zoneTz :=
    match aw with
    | .only newTz => newTz
    | .any => tz

  (DateTime.ofPlainDateTime · (ZoneRules.ofTimeZone zoneTz)) <$> datetime

end DateBuilder

private def parseWithDate (date : DateBuilder) (config : FormatConfig) (mod : FormatPart) (rest : FormatString) : Parser DateBuilder := do
  match mod with
  | .modifier s => do
    let res ← parseWith config (reservedDigits rest) s
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

private def parser (format : FormatString) (config : FormatConfig) (aw : Awareness) : Parser DateTime :=
  let rec go (builder : DateBuilder) (x : FormatString) : Parser DateTime :=
    match x with
    | x :: xs => parseWithDate builder config x xs >>= (go · xs)
    | [] =>
      match builder.build aw config.dateformat with
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
      let res ← parseWith config (reservedDigits xs) x
      go xs (func res)
    | .string s :: xs => skipString s *> (go xs func)
    | [] =>
        match func with
        | some res => eof *> pure res
        | none => fail "invalid date."
  go format func

/--
Parses the input string into a `DateTime`.
-/
def parse (format : GenericFormat aw) (input : String) : Except String DateTime :=
  (parser format.string format.config aw <* eof).run input

/--
Parses the input string into a `DateTime` and panics if its wrong.
-/
def parse! (format : GenericFormat aw) (input : String) : DateTime :=
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
  let dateformat := format.config.dateformat
  let rec go (data : String) : (format : FormatString) → Option String
    | .modifier x :: xs => do go (data ++ formatWith dateformat x (← getInfo x)) xs
    | .string x :: xs => go (data ++ x) xs
    | [] => some data
  go "" format.string

/--
Formats the given parts of a date and time: a date, a time of day and a zone. Returns `none` when the
format needs a part that is missing, such as an hour for a date alone.
-/
def formatParts (format : GenericFormat aw) (date : Option PlainDate) (time : Option PlainTime)
    (zone : Option TimeZone) : Option String :=
  format.formatGeneric (fieldValue? format.config.dateformat date time zone)

/--
Formats a `DateTime` value into a string using the given `GenericFormat`.
-/
def format (format : GenericFormat aw) (date : DateTime) : String :=
  let date :=
    match aw with
    | .any => date
    | .only tz => date.convertZoneRules (TimeZone.ZoneRules.ofTimeZone tz)
  let pdt := date.toPlainDateTime
  -- A `DateTime` has every part, so no field is missing.
  format.formatParts (some pdt.date) (some pdt.time) (some date.timezone) |>.getD ""

/--
Constructs a `FormatType` function to format a date into a string using a `GenericFormat`.
-/
def formatBuilder (format : GenericFormat aw) : FormatType String format.string :=
  let dateformat := format.config.dateformat
  let rec go (data : String) : (format : FormatString) → FormatType String format
    | .modifier x :: xs => fun res => go (data ++ formatWith dateformat x res) xs
    | .string x :: xs => go (data ++ x) xs
    | [] => data
  go "" format.string

end GenericFormat

end Time
