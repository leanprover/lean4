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

private def specParse (s : String) : Except String FormatString :=
  specParser.run s

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

private def rightTruncate (size : Nat)  (n : Int) (cut : Bool := false) : String :=
  let (sign, n) := if n < 0 then ("-", -n) else ("", n)

  let numStr := toString n
  if numStr.length > size then
    sign ++ if cut then numStr.take size |>.copy else numStr
  else
    sign ++ rightPadAscii size '0' numStr

private def eraIndex : Year.Era → Fin 2
  | .bce => 0
  | .ce => 1

private def formatMonthLong (symbols : DateFormatSymbols) (month : Month.Ordinal) : String :=
  symbols.monthLong.get (month.sub 1 |>.toFin (by decide))

private def formatMonthShort (symbols : DateFormatSymbols) (month : Month.Ordinal) : String :=
  symbols.monthShort.get (month.sub 1 |>.toFin (by decide))

private def formatMonthNarrow (symbols : DateFormatSymbols) (month : Month.Ordinal) : String :=
  symbols.monthNarrow.get (month.sub 1 |>.toFin (by decide))

private def formatWeekdayLong (symbols : DateFormatSymbols) (wd : Weekday) : String :=
  symbols.weekdayLong.get (wd.toOrdinal.sub 1 |>.toFin (by decide))

private def formatWeekdayShort (symbols : DateFormatSymbols) (wd : Weekday) : String :=
  symbols.weekdayShort.get (wd.toOrdinal.sub 1 |>.toFin (by decide))

private def formatWeekdayNarrow (symbols : DateFormatSymbols) (wd : Weekday) : String :=
  symbols.weekdayNarrow.get (wd.toOrdinal.sub 1 |>.toFin (by decide))

private def formatWeekdayTwoLetter (symbols : DateFormatSymbols) (wd : Weekday) : String :=
  symbols.weekdayTwoLetter.get (wd.toOrdinal.sub 1 |>.toFin (by decide))

private def formatEraShort (symbols : DateFormatSymbols) (era : Year.Era) : String :=
  symbols.eraShort.get (eraIndex era)

private def formatEraLong (symbols : DateFormatSymbols) (era : Year.Era) : String :=
  symbols.eraLong.get (eraIndex era)

private def formatEraNarrow (symbols : DateFormatSymbols) (era : Year.Era) : String :=
  symbols.eraNarrow.get (eraIndex era)

private def formatQuarterNumber : Month.Quarter → String
  | ⟨1, _⟩ => "1"
  | ⟨2, _⟩ => "2"
  | ⟨3, _⟩ => "3"
  | ⟨4, _⟩ => "4"

private def formatQuarterShort (symbols : DateFormatSymbols) (q : Month.Quarter) : String :=
  symbols.quarterShort.get (q.sub 1 |>.toFin (by decide))

private def formatQuarterLong (symbols : DateFormatSymbols) (q : Month.Quarter) : String :=
  symbols.quarterLong.get (q.sub 1 |>.toFin (by decide))

private def formatQuarterNarrow (symbols : DateFormatSymbols) (q : Month.Quarter) : String :=
  symbols.quarterNarrow.get (q.sub 1 |>.toFin (by decide))

private def formatMarkerShort (symbols : DateFormatSymbols) (marker : HourMarker) : String :=
  match marker with
  | .am => symbols.amShort
  | .pm => symbols.pmShort

private def formatMarkerLong (symbols : DateFormatSymbols) (marker : HourMarker) : String :=
  match marker with
  | .am => symbols.amLong
  | .pm => symbols.pmLong

private def formatMarkerNarrow (symbols : DateFormatSymbols) (marker : HourMarker) : String :=
  match marker with
  | .am => symbols.amNarrow
  | .pm => symbols.pmNarrow

private def formatDayPeriod (dp : DayPeriodSymbols) (period : DayPeriod) : String :=
  match period with
  | .am       => dp.am
  | .pm       => dp.pm
  | .noon     => dp.noon
  | .midnight => dp.midnight

private def extendedDayPeriodIndex : ExtendedDayPeriod → Fin 6
  | .midnight  => 0
  | .night     => 1
  | .morning   => 2
  | .noon      => 3
  | .afternoon => 4
  | .evening   => 5

private def formatExtendedDayPeriod (arr : Vector String 6) (period : ExtendedDayPeriod) : String :=
  arr.get (extendedDayPeriodIndex period)

private def toSigned (data : Int) : String :=
  if data < 0 then toString data else "+" ++ toString data

private inductive Reason
  | yes
  | no
  | optional
deriving BEq

private def toIsoString (offset : Offset) (withMinutes : Reason) (withSeconds : Reason) (colon : Bool) (padHour : Bool := true) : String :=
  let (sign, time) := if offset.second.val ≥ 0 then ("+", offset.second) else ("-", -offset.second)
  let time := PlainTime.ofSeconds time
  let pad := leftPadAscii 2 '0' ∘ toString

  let hourStr := if padHour then pad time.hour.val else toString time.hour.val
  let data := s!"{sign}{hourStr}"

  let data :=
    if withMinutes == .yes ∨ (withMinutes == .optional ∧ time.minute.val ≠ 0) then
      s!"{data}{if colon then ":" else ""}{pad time.minute.val}"
    else
      data

  let data :=
    if withSeconds == .yes ∨ (withSeconds == .optional ∧ time.second.val ≠ 0) then
      s!"{data}{if colon then ":" else ""}{pad time.second.val}"
    else
      data

  data

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
  | .G format =>
    match format with
    | .short => formatEraShort dateformat.symbols data
    | .full  => formatEraLong dateformat.symbols data
    | .narrow => formatEraNarrow dateformat.symbols data
    | .twoLetterShort => formatEraShort dateformat.symbols data
  | .y format =>
    let info := data.toInt
    let info := if info ≤ 0 then -info + 1 else info
    match format with
    | .any      => pad 0 info
    | .twoDigit => pad 2 (info % 100)
    | .fourDigit => pad 4 info
    | .extended n => pad n info
  | .u format =>
    match format with
    | .any      => pad 0 (data.toInt)
    | .twoDigit => pad 2 (data.toInt % 100)
    | .fourDigit => pad 4 data.toInt
    | .extended n => pad n data.toInt
  | .Y format =>
    let info := data.toInt
    let info := if info ≤ 0 then -info + 1 else info
    match format with
    | .any      => pad 0 info
    | .twoDigit => pad 2 (info % 100)
    | .fourDigit => pad 4 info
    | .extended n => pad n info
  | .D format =>
    pad format.padding data.snd.val
  | .M format | .L format =>
    match format with
    | .inl fmt  => pad fmt.padding data.val
    | .inr .short => formatMonthShort dateformat.symbols data
    | .inr .full  => formatMonthLong dateformat.symbols data
    | .inr .narrow => formatMonthNarrow dateformat.symbols data
    | .inr .twoLetterShort => formatMonthShort dateformat.symbols data
  | .d format =>
    pad format.padding data.val
  | .Q format | .q format =>
    match format with
    | .inl fmt  => pad fmt.padding data.val
    | .inr .short  => formatQuarterShort dateformat.symbols data
    | .inr .full   => formatQuarterLong dateformat.symbols data
    | .inr .narrow => formatQuarterNarrow dateformat.symbols data
    | .inr .twoLetterShort => formatQuarterNumber data
  | .w format =>
    pad format.padding data.val
  | .W format =>
    pad format.padding data.val
  | .E format =>
    match format with
    | .short  => formatWeekdayShort dateformat.symbols data
    | .full   => formatWeekdayLong dateformat.symbols data
    | .narrow => formatWeekdayNarrow dateformat.symbols data
    | .twoLetterShort => formatWeekdayTwoLetter dateformat.symbols data
  | .e format | .c format =>
    match format with
    | .inl fmt =>
      let firstOrd : Int := dateformat.firstDayOfWeek.toOrdinal.val
      let dayOrd : Int := data.toOrdinal.val
      pad fmt.padding ((dayOrd - firstOrd + 7) % 7 + 1)
    | .inr .short  => formatWeekdayShort dateformat.symbols data
    | .inr .full   => formatWeekdayLong dateformat.symbols data
    | .inr .narrow => formatWeekdayNarrow dateformat.symbols data
    | .inr .twoLetterShort => formatWeekdayTwoLetter dateformat.symbols data
  | .F format =>
    pad format.padding data.val
  | .a format =>
    match format with
    | .short => formatMarkerShort dateformat.symbols data
    | .full => formatMarkerShort dateformat.symbols data
    | .narrow => formatMarkerNarrow dateformat.symbols data
    | .twoLetterShort => formatMarkerShort dateformat.symbols data
  | .b format =>
    match format with
    | .short  => formatDayPeriod dateformat.symbols.dayPeriodShort data
    | .full   => formatDayPeriod dateformat.symbols.dayPeriodLong data
    | .narrow => formatDayPeriod dateformat.symbols.dayPeriodNarrow data
    | .twoLetterShort => formatDayPeriod dateformat.symbols.dayPeriodShort data
  | .B format =>
    match format with
    | .short  => formatExtendedDayPeriod dateformat.symbols.extendedDayPeriodShort data
    | .full   => formatExtendedDayPeriod dateformat.symbols.extendedDayPeriodLong data
    | .narrow => formatExtendedDayPeriod dateformat.symbols.extendedDayPeriodNarrow data
    | .twoLetterShort => formatExtendedDayPeriod dateformat.symbols.extendedDayPeriodShort data
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
  | .V format =>
    match format with
    | .unknown => "unk"
    | .short   => data
    | .full    => data
  | .z format =>
    match format with
    | .short => data
    | .full  => data
  | .v format =>
    match format with
    | .short => data
    | .full  => data
  | .O format =>
    match format with
    | .short =>
      if data.second == 0 then "GMT"
      else
        let (sign, time) := if data.second.val ≥ 0 then ("+", data.second) else ("-", -data.second)
        let t := PlainTime.ofSeconds time
        let pad := leftPadAscii 2 '0' ∘ toString
        if t.minute.val == 0
          then s!"GMT{sign}{t.hour.val}"
          else s!"GMT{sign}{t.hour.val}:{pad t.minute.val}"
    | .full  =>
      if data.second == 0 then "GMT" else s!"GMT{toIsoString data .yes .no true}"
  | .X format =>
    if data.second == 0 then
      "Z"
    else
      match format with
        | .hour => toIsoString data .optional .no false
        | .hourMinute => toIsoString data .yes .no false
        | .hourMinuteColon => toIsoString data .yes .no true
        | .hourMinuteSecond => toIsoString data .yes .optional false
        | .hourMinuteSecondColon => toIsoString data .yes .optional true
  | .x format =>
    match format with
    | .hour =>
      toIsoString data .optional .no false
    | .hourMinute =>
      toIsoString data .yes .no false
    | .hourMinuteColon =>
      toIsoString data .yes .no true
    | .hourMinuteSecond =>
      toIsoString data .yes .optional false
    | .hourMinuteSecondColon =>
      toIsoString data .yes .optional true
  | .Z format =>
    match format with
    | .hourMinute =>
      toIsoString data .yes .optional false
    | .full =>
      if data.second.val = 0
        then "GMT"
        else s!"GMT{toIsoString data .yes .no true}"
    | .hourMinuteSecondColon =>
      if data.second == 0
        then "Z"
        else toIsoString data .yes .optional true

private def dateFromModifier (dateformat : DateFormat) (date : DateTime) : TypeFormat modifier :=
  let firstDay := dateformat.firstDayOfWeek
  let minDays := dateformat.minimalDaysInFirstWeek
  let tz := date.timezone
  match modifier with
  | .G _ => date.era
  | .y _ => date.year
  | .u _ => date.year
  | .Y _ => date.weekYear firstDay minDays
  | .D _ => Sigma.mk _ date.dayOfYear
  | .M _ | .L _ => date.month
  | .d _ => date.day
  | .Q _ | .q _ => date.quarter
  | .w _ => date.weekOfYear firstDay minDays
  | .W _ => date.weekOfMonth firstDay
  | .E _ | .e _ | .c _ => date.weekday
  | .F _ => date.alignedWeekOfMonth
  | .a _ => HourMarker.ofOrdinal date.hour
  | .b _ => classifyDayPeriod date.hour date.minute date.date.get.time.second
  | .B _ => classifyExtendedDayPeriod date.hour date.minute date.date.get.time.second
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
  | .V .unknown => "unk"
  | .V .short =>
    if tz.name.startsWith "+" || tz.name.startsWith "-"
      then s!"GMT{toIsoString tz.offset .yes .no true}"
      else tz.name
  | .V .full =>
    if tz.name.startsWith "+" || tz.name.startsWith "-"
      then s!"GMT{toIsoString tz.offset .yes .no true}"
      else tz.name
  | .z .short =>
    if tz.abbreviation.startsWith "+" || tz.abbreviation.startsWith "-"
      then s!"GMT{toIsoString tz.offset .yes .no true}"
      else tz.abbreviation
  | .z .full =>
    if tz.name.startsWith "+" || tz.name.startsWith "-"
      then s!"GMT{toIsoString tz.offset .yes .no true}"
      else tz.name
  | .v .short =>
    if tz.abbreviation.startsWith "+" || tz.abbreviation.startsWith "-"
      then s!"GMT{toIsoString tz.offset .yes .no true}"
      else tz.abbreviation
  | .v .full =>
    if tz.name.startsWith "+" || tz.name.startsWith "-"
      then s!"GMT{toIsoString tz.offset .yes .no true}"
      else tz.name
  | .O _ => tz.offset
  | .X _ => tz.offset
  | .x _ => tz.offset
  | .Z _ => tz.offset

private def parseFromSymbols {α : Type} (pairs : Array (String × α)) : Parser α :=
  pairs.foldl (fun acc (s, v) => acc <|> pstring s *> pure v) (fail "no match")

private def monthPairs (arr : Vector String 12) : Array (String × Month.Ordinal) :=
  arr.mapFinIdx (fun idx val n => (val, Bounded.LE.ofFin ⟨idx, n⟩ |>.add 1)) |>.toArray

private def weekdayOfIndex : Nat → Weekday
  | 0 => .sunday
  | 1 => .monday
  | 2 => .tuesday
  | 3 => .wednesday
  | 4 => .thursday
  | 5 => .friday
  | _ => .saturday

private def weekdayPairs (arr : Vector String 7) : Array (String × Weekday) :=
  arr.mapFinIdx (fun idx val n => (val, .ofOrdinal <| Bounded.LE.ofFin ⟨idx, n⟩ |>.add 1)) |>.toArray

private def eraOfIndex : Nat → Year.Era
  | 0 => .bce
  | _ => .ce

private def eraPairs (arr : Vector String 2) : Array (String × Year.Era) :=
  arr.mapFinIdx (fun idx val _ => (val, eraOfIndex idx)) |>.toArray

private def quarterPairs (arr : Vector String 4) : Array (String × Month.Quarter) :=
  arr.mapFinIdx (fun idx val n => (val, Bounded.LE.ofFin ⟨idx, n⟩ |>.add 1)) |>.toArray

private def parseMonthLong (symbols : DateFormatSymbols) : Parser Month.Ordinal :=
  parseFromSymbols (monthPairs symbols.monthLong)

/--
Parses a short month name using the given locale symbols and returns the corresponding `Month.Ordinal`.
-/
def parseMonthShort (symbols : DateFormatSymbols) : Parser Month.Ordinal :=
  parseFromSymbols (monthPairs symbols.monthShort)

private def parseMonthNarrow (symbols : DateFormatSymbols) : Parser Month.Ordinal :=
  parseFromSymbols (monthPairs symbols.monthNarrow)

private def parseWeekdayLong (symbols : DateFormatSymbols) : Parser Weekday :=
  parseFromSymbols (weekdayPairs symbols.weekdayLong)

private def parseWeekdayShort (symbols : DateFormatSymbols) : Parser Weekday :=
  parseFromSymbols (weekdayPairs symbols.weekdayShort)

private def parseWeekdayNarrow (symbols : DateFormatSymbols) : Parser Weekday :=
  parseFromSymbols (weekdayPairs symbols.weekdayNarrow)

private def parseWeekdayTwoLetter (symbols : DateFormatSymbols) : Parser Weekday :=
  parseFromSymbols (weekdayPairs symbols.weekdayTwoLetter)

private def parseEraShort (symbols : DateFormatSymbols) : Parser Year.Era :=
  parseFromSymbols (eraPairs symbols.eraShort)

private def parseEraLong (symbols : DateFormatSymbols) : Parser Year.Era :=
  parseFromSymbols (eraPairs symbols.eraLong)

private def parseEraNarrow (symbols : DateFormatSymbols) : Parser Year.Era :=
  parseFromSymbols (eraPairs symbols.eraNarrow)

private def parseQuarterNumber : Parser Month.Quarter
   := pstring "1" *> pure ⟨1, by decide⟩
  <|> pstring "2" *> pure ⟨2, by decide⟩
  <|> pstring "3" *> pure ⟨3, by decide⟩
  <|> pstring "4" *> pure ⟨4, by decide⟩

private def parseQuarterLong (symbols : DateFormatSymbols) : Parser Month.Quarter :=
  parseFromSymbols (quarterPairs symbols.quarterLong)

private def parseQuarterShort (symbols : DateFormatSymbols) : Parser Month.Quarter :=
  parseFromSymbols (quarterPairs symbols.quarterShort)

private def parseQuarterNarrow (symbols : DateFormatSymbols) : Parser Month.Quarter :=
  parseFromSymbols (quarterPairs symbols.quarterNarrow)

private def parseMarkerShort (symbols : DateFormatSymbols) : Parser HourMarker :=
  (pstring symbols.amShort *> pure .am) <|> (pstring symbols.pmShort *> pure .pm)

private def parseMarkerLong (symbols : DateFormatSymbols) : Parser HourMarker :=
  (pstring symbols.amLong *> pure .am) <|> (pstring symbols.pmLong *> pure .pm)

private def parseMarkerNarrow (symbols : DateFormatSymbols) : Parser HourMarker :=
  (pstring symbols.amNarrow *> pure .am) <|> (pstring symbols.pmNarrow *> pure .pm)

private def parseDayPeriodFrom (dp : DayPeriodSymbols) : Parser DayPeriod :=
    pstring dp.midnight *> pure .midnight
  <|> pstring dp.noon   *> pure .noon
  <|> pstring dp.am     *> pure .am
  <|> pstring dp.pm     *> pure .pm

private def parseExtendedDayPeriodFrom (arr : Vector String 6) : Parser ExtendedDayPeriod :=
  let pairs : Array (String × ExtendedDayPeriod) := #[
    (arr.get 0, .midnight), (arr.get 1, .night),     (arr.get 2, .morning),
    (arr.get 3, .noon),     (arr.get 4, .afternoon),  (arr.get 5, .evening)
  ]
  parseFromSymbols pairs

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
  String.toNat! <$> rightPadAscii pad '0' <$> exactlyChars (satisfy Char.isDigit) size

private def parseIdentifier : Parser String :=
  many1Chars (satisfy (fun x => x.isAlpha ∨ x.isDigit ∨ x = '_' ∨ x = '-' ∨ x = '/'))

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

private def parseWith (config : FormatConfig) : (mod : Modifier) → Parser (TypeFormat mod)
  | .G format =>
    match format with
    | .short | .twoLetterShort => parseEraShort config.dateformat.symbols
    | .full => parseEraLong config.dateformat.symbols
    | .narrow => parseEraNarrow config.dateformat.symbols
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
  | .Y format =>
    match format with
    | .any => parseSigned <| parseAtLeastNum 1
    | .twoDigit => (2000 + ·) <$> Int.ofNat <$> parseNum 2
    | .fourDigit => parseSigned <| parseNum 4
    | .extended n => parseSigned <| parseNum n
  | .D format => Sigma.mk true <$> parseNatToBounded (parseFlexibleNum format.padding)
  | .M format | .L format =>
    match format with
    | .inl fmt  => parseNatToBounded (parseFlexibleNum fmt.padding)
    | .inr .short | .inr .twoLetterShort => parseMonthShort config.dateformat.symbols
    | .inr .full   => parseMonthLong config.dateformat.symbols
    | .inr .narrow => parseMonthNarrow config.dateformat.symbols
  | .d format => parseNatToBounded (parseFlexibleNum format.padding)
  | .Q format | .q format =>
    match format with
    | .inl fmt  => parseNatToBounded (parseFlexibleNum fmt.padding)
    | .inr .short => parseQuarterShort config.dateformat.symbols
    | .inr .full  => parseQuarterLong config.dateformat.symbols
    | .inr .narrow | .inr .twoLetterShort => parseQuarterNarrow config.dateformat.symbols
  | .w format => parseNatToBounded (parseFlexibleNum format.padding)
  | .W format => parseNatToBounded (parseFlexibleNum format.padding)
  | .E format =>
    match format with
    | .short | .twoLetterShort => parseWeekdayShort config.dateformat.symbols
    | .full => parseWeekdayLong config.dateformat.symbols
    | .narrow => parseWeekdayNarrow config.dateformat.symbols
  | .e format | .c format =>
    match format with
    | .inl fmt => do
      let n ← parseFlexibleNum fmt.padding
      if ¬ (1 ≤ n ∧ n ≤ 7) then fail "need a natural number in the interval of 1 to 7"
      let firstOrd : Int := config.dateformat.firstDayOfWeek.toOrdinal.val
      let absOrd : Int := ((n : Int) - 1 + firstOrd - 1) % 7 + 1
      return Weekday.ofOrdinal (Bounded.LE.ofNatWrapping absOrd (by decide))
    | .inr .short => parseWeekdayShort config.dateformat.symbols
    | .inr .full  => parseWeekdayLong config.dateformat.symbols
    | .inr .narrow => parseWeekdayNarrow config.dateformat.symbols
    | .inr .twoLetterShort => parseWeekdayTwoLetter config.dateformat.symbols
  | .F format => parseNatToBounded (parseFlexibleNum format.padding)
  | .a format =>
    match format with
    | .short | .twoLetterShort => parseMarkerShort config.dateformat.symbols
    | .full => parseMarkerLong config.dateformat.symbols
    | .narrow => parseMarkerNarrow config.dateformat.symbols
  | .b format =>
    match format with
    | .short | .twoLetterShort => parseDayPeriodFrom config.dateformat.symbols.dayPeriodShort
    | .full => parseDayPeriodFrom config.dateformat.symbols.dayPeriodLong
    | .narrow => parseDayPeriodFrom config.dateformat.symbols.dayPeriodNarrow
  | .B format =>
    match format with
    | .short | .twoLetterShort => parseExtendedDayPeriodFrom config.dateformat.symbols.extendedDayPeriodShort
    | .full => parseExtendedDayPeriodFrom config.dateformat.symbols.extendedDayPeriodLong
    | .narrow => parseExtendedDayPeriodFrom config.dateformat.symbols.extendedDayPeriodNarrow
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
  | .V format =>
    match format with
    | .unknown => pstring "unk" *> pure "unk"
    | .short | .full => parseIdentifier
  | .z format =>
    match format with
    | .short | .full => parseIdentifier
  | .v format =>
    match format with
    | .short | .full => parseIdentifier
  | .O format =>
    match format with
    | .short => pstring "GMT" *> parseOffset .optional .no true
    | .full  => pstring "GMT" *> parseOffset .yes .optional true
  | .X format =>
    let p : Parser Offset :=
      match format with
        | .hour => parseOffset .optional .no false
        | .hourMinute => parseOffset .yes .no false
        | .hourMinuteColon => parseOffset .yes .no true
        | .hourMinuteSecond => parseOffset .yes .optional false
        | .hourMinuteSecondColon => parseOffset .yes .optional true
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


private def formatPartWithDate (dateformat : DateFormat) (date : DateTime) (part : FormatPart) : String :=
  match part with
  | .modifier mod => formatWith dateformat mod (dateFromModifier dateformat date)
  | .string s => s

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
  | .v .short => { date with v := some data }
  | .O _  => { date with O := some data }
  | .X _  => { date with X := some data }
  | .x _  => { date with x := some data }
  | .Z _  => { date with Z := some data }

private def convertYearAndEra (year : Year.Offset) : Year.Era → Year.Offset
  | .ce => year
  | .bce => -(year + 1)

/-- Infer an `HourMarker` from a `DayPeriod` parsed by `b`. -/
private def markerOfDayPeriod : DayPeriod → HourMarker
  | .am | .midnight => .am
  | .pm | .noon     => .pm

/-- Infer an `HourMarker` from an `ExtendedDayPeriod` parsed by `B`. -/
private def markerOfExtendedDayPeriod : ExtendedDayPeriod → HourMarker
  | .midnight | .night | .morning => .am
  | .noon | .afternoon | .evening => .pm

private def build (builder : DateBuilder) (aw : Awareness) : Option DateTime :=
  let offset := builder.O <|> builder.X <|> builder.x <|> builder.Z |>.getD Offset.zero

  let tz : TimeZone := {
    offset,
    name := builder.V <|> builder.v <|> builder.z |>.getD (offset.toIsoString true),
    abbreviation := builder.zabbrev |>.getD (offset.toIsoString true),
    isDST := false,
  }

  let month := builder.M <|> builder.L |>.getD 0
  let day := builder.d |>.getD 0
  let era := (builder.G.getD .ce)

  let year
    := builder.u
    <|> ((convertYearAndEra · era) <$> builder.y)
    <|> builder.Y
    |>.getD 0

  -- Derive hour marker from `a`, then fall back to `b` and `B`.
  let markerOpt : Option HourMarker :=
    builder.a
    <|> (markerOfDayPeriod <$> builder.b)
    <|> (markerOfExtendedDayPeriod <$> builder.B)

  let hour : Option (Bounded.LE 0 23) :=
    if let some marker := markerOpt then
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

  let zoneTz :=
    match aw with
    | .only newTz => newTz
    | .any => tz

  (DateTime.ofPlainDateTime · (ZoneRules.ofTimeZone zoneTz)) <$> datetime

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
def format (format : GenericFormat aw) (date : DateTime) : String :=
  let dateformat := format.config.dateformat
  let mapper (part : FormatPart) :=
    match aw with
    | .any => formatPartWithDate dateformat date part
    | .only tz => formatPartWithDate dateformat (date.convertZoneRules (TimeZone.ZoneRules.ofTimeZone tz)) part

  format.string.map mapper
  |> String.join

private def parser (format : FormatString) (config : FormatConfig) (aw : Awareness) : Parser DateTime :=
  let rec go (builder : DateBuilder) (x : FormatString) : Parser DateTime :=
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
