/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Time.Date
import Std.Time.Time
import Std.Time.DateTime
import Std.Time.Zoned
import Lean.Data.Parsec

namespace Std
namespace Time

open Lean.Parsec Lean Time Date TimeZone DateTime

/--
The `Modifier` inductive type represents various formatting options for date and time components.
These modifiers are typically used in formatting functions to generate human-readable date and time strings.

- `YYYY`: Four-digit year (e.g., 2024).
- `YY`: Two-digit year (e.g., 24 for 2024).
- `MMMM`: Full month name (e.g., January, February).
- `MMM`: Abbreviated month name (e.g., Jan, Feb).
- `MM`: Two-digit month (e.g., 01 for January).
- `M`: One or two-digit month (e.g., 1 for January, 10 for October).
- `DD`: Two-digit day of the month (e.g., 01, 02).
- `D`: One or two-digit day of the month (e.g., 1, 2).
- `d`: One or two digit day of the month with space padding at the beggining (e.g.  1, 12).
- `EEEE`: Full name of the day of the week (e.g., Monday, Tuesday).
- `EEE`: Abbreviated day of the week (e.g., Mon, Tue).
- `hh`: Two-digit hour in 24-hour format (e.g., 01, 02).
- `h`: One or two-digit hour in 24-hour format (e.g., 1, 2).
- `HH`: Two-digit hour in 12-hour format (e.g., 13, 14).
- `H`: One or two-digit hour in 12-hour format (e.g., 1, 2).
- `AA`: Uppercase AM/PM indicator (e.g., AM, PM).
- `aa`: Lowercase am/pm indicator (e.g., am, pm).
- `mm`: Two-digit minute (e.g., 01, 02).
- `m`: One or two-digit minute (e.g., 1, 2).
- `sss`: Three-digit milliseconds (e.g., 001, 202).
- `ss`: Two-digit second (e.g., 01, 02).
- `s`: One or two-digit second (e.g., 1, 2).
- `ZZZZZ`: Full timezone offset including hours and minutes (e.g., +03:00).
- `ZZZZ`: Timezone offset including hours and minutes without the colon (e.g., +0300).
- `ZZZ`: Like ZZZZ but with a special case "UTC" for UTC.
- `Z`: Like ZZZZZ but with a special case "Z" for UTC.
- `z`: Name of the time-zone like (Brasilia Standard Time).
-/
inductive Modifier
  | YYYY
  | YY
  | MMMM
  | MMM
  | MM
  | M
  | DD
  | D
  | d
  | EEEE
  | EEE
  | hh
  | h
  | HH
  | H
  | AA
  | aa
  | mm
  | m
  | sss
  | ss
  | s
  | ZZZZZ
  | ZZZZ
  | ZZZ
  | Z
  | z
  deriving Repr

/--
The part of a formatting string. a string is just a text and a modifier is in the format `%0T` where
0 is the quantity of left pad and `T` the `Modifier`.
-/
inductive FormatPart
  | string (val : String)
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

inductive Awareness
  | only : TimeZone → Awareness
  | any

namespace Awareness

instance : Coe TimeZone Awareness where
  coe := .only

@[simp]
def type (x : Awareness) : Type :=
  match x with
  | .any => ZonedDateTime
  | .only tz => DateTime tz

instance : Inhabited (type aw) where
  default := by
    simp [type]
    split <;> exact Inhabited.default

def getD (x : Awareness) (default : TimeZone) : TimeZone :=
  match x with
  | .any => default
  | .only tz => tz

end Awareness

structure Format (awareness : Awareness) where
  string : FormatString
  deriving Inhabited, Repr

private def isNonLetter : Char → Bool := not ∘ Char.isAlpha

private def parseModifier : Lean.Parsec Modifier
  :=  pstring "YYYY" *> pure .YYYY
  <|> pstring "YY" *> pure .YY
  <|> pstring "MMMM" *> pure .MMMM
  <|> pstring "MMM" *> pure .MMM
  <|> pstring "MM" *> pure .MM
  <|> pstring "M" *> pure .M
  <|> pstring "DD" *> pure .DD
  <|> pstring "D" *> pure .D
  <|> pstring "d" *> pure .d
  <|> pstring "EEEE" *> pure .EEEE
  <|> pstring "EEE" *> pure .EEE
  <|> pstring "hh" *> pure .hh
  <|> pstring "h" *> pure .h
  <|> pstring "HH" *> pure .HH
  <|> pstring "H" *> pure .H
  <|> pstring "AA" *> pure .AA
  <|> pstring "aa" *> pure .aa
  <|> pstring "mm" *> pure .mm
  <|> pstring "m" *> pure .m
  <|> pstring "sss" *> pure .sss
  <|> pstring "ss" *> pure .ss
  <|> pstring "s" *> pure .s
  <|> pstring "ZZZZZ" *> pure .ZZZZZ
  <|> pstring "ZZZZ" *> pure .ZZZZ
  <|> pstring "ZZZ" *> pure .ZZZ
  <|> pstring "Z" *> pure .Z
  <|> pstring "z" *> pure .z

def isFormatStart : Char → Bool := Char.isAlpha

private def pnumber : Lean.Parsec Nat := do
  let numbers ← manyChars digit
  return numbers.foldl (λacc char => acc * 10 + (char.toNat - 48)) 0

private def parseFormatPart : Lean.Parsec FormatPart
  := (.modifier <$> parseModifier)
  <|> (pchar '\\') *> anyChar <&> (.string ∘ toString)
  <|> (pchar '\"' *>  many1Chars (satisfy (· ≠ '\"')) <* pchar '\"') <&> .string
  <|> (pchar '\'' *>  many1Chars (satisfy (· ≠ '\'')) <* pchar '\'') <&> .string
  <|> many1Chars (satisfy (fun x => ¬isFormatStart x ∧ x ≠ '\'' ∧ x ≠ '\"')) <&> .string

private def specParser : Lean.Parsec FormatString :=
  (Array.toList <$> Lean.Parsec.many parseFormatPart) <* eof

private def specParse (s: String) : Except String FormatString :=
  specParser.run s

-- Pretty printer

private def unabbrevMonth (month: Month.Ordinal) : String :=
  match month.val, month.property with
  | 1, _ => "January"
  | 2, _ => "February"
  | 3, _ => "March"
  | 4, _ => "April"
  | 5, _ => "May"
  | 6, _ => "June"
  | 7, _ => "July"
  | 8, _ => "August"
  | 9, _ => "September"
  | 10, _ => "October"
  | 11, _ => "November"
  | 12, _ => "December"

private def abbrevMonth (month: Month.Ordinal) : String :=
  match month.val, month.property with
  | 1, _ => "Jan"
  | 2, _ => "Feb"
  | 3, _ => "Mar"
  | 4, _ => "Apr"
  | 5, _ => "May"
  | 6, _ => "Jun"
  | 7, _ => "Jul"
  | 8, _ => "Aug"
  | 9, _ => "Sep"
  | 10, _ => "Oct"
  | 11, _ => "Nov"
  | 12, _ => "Dec"

private def abbrevDayOfWeek (day: Weekday) : String :=
  match day with
  | .sun => "Sun"
  | .mon => "Mon"
  | .tue => "Tue"
  | .wed => "Wed"
  | .thu => "Thu"
  | .fri => "Fri"
  | .sat => "Sat"

private def dayOfWeek (day: Weekday) : String :=
  match day with
  | .sun => "Sunday"
  | .mon => "Monday"
  | .tue => "Tuesday"
  | .wed => "Wednesday"
  | .thu => "Thusday"
  | .fri => "Friday"
  | .sat => "Saturday"

private def leftPad (n : Nat) (a : Char) (s : String) : String :=
  "".pushn a (n - s.length) ++ s

private def formatWithDate (date : DateTime tz) : Modifier → String
  | .YYYY  => s!"{leftPad 4 '0' (toString date.year)}"
  | .YY    => s!"{leftPad 2 '0' (toString $ date.year.toNat % 100)}"
  | .MMMM  => unabbrevMonth date.month
  | .MMM   => abbrevMonth date.month
  | .MM    => s!"{leftPad 2 '0' (toString $ date.month.toNat)}"
  | .M     => s!"{date.month.toNat}"
  | .DD    => s!"{leftPad 2 '0' (toString $ date.day.toNat)}"
  | .D     => s!"{date.day.toNat}"
  | .d     => s!"{leftPad 2 ' ' $ toString date.day.toNat}"
  | .EEEE  => dayOfWeek date.weekday
  | .EEE   => abbrevDayOfWeek date.weekday
  | .hh    => s!"{leftPad 2 '0' (toString date.hour.toNat)}"
  | .h     => s!"{date.hour.toNat}"
  | .HH    => let hour := date.hour.val % 12; if hour == 0 then "12" else s!"{leftPad 2 '0' $ toString hour}"
  | .H     => let hour := date.hour.val % 12; if hour == 0 then "12" else s!"{hour}"
  | .AA    => if date.hour.toNat < 12 then "AM" else "PM"
  | .aa    => if date.hour.toNat < 12 then "am" else "pm"
  | .mm    => s!"{leftPad 2 '0' $ toString date.minute.toNat}"
  | .m     => s!"{date.minute.toNat}"
  | .sss    => s!"{leftPad 3 '0' $ toString date.milliseconds.toNat}"
  | .ss    => s!"{leftPad 2 '0' $ toString date.second.toNat}"
  | .s     => s!"{date.second.toNat}"
  | .ZZZZZ => tz.offset.toIsoString true
  | .ZZZZ  => tz.offset.toIsoString false
  | .ZZZ   => if tz.offset.second.val = 0 then "UTC" else tz.offset.toIsoString false
  | .Z     => if tz.offset.second.val = 0 then "Z" else tz.offset.toIsoString true
  | .z     => tz.name

private def formatPartWithDate (date : DateTime z) : FormatPart → String
  | .string s => s
  | .modifier t => formatWithDate date t

-- Parser

@[simp]
private def SingleFormatType : Modifier → Type
  | .YYYY => Year.Offset
  | .YY => Year.Offset
  | .MMMM => Month.Ordinal
  | .MMM => Month.Ordinal
  | .MM => Month.Ordinal
  | .M => Month.Ordinal
  | .DD => Day.Ordinal
  | .D => Day.Ordinal
  | .d => Day.Ordinal
  | .EEEE => Weekday
  | .EEE => Weekday
  | .hh => Hour.Ordinal
  | .h => Hour.Ordinal
  | .HH => Hour.Ordinal
  | .H => Hour.Ordinal
  | .AA => HourMarker
  | .aa => HourMarker
  | .mm => Minute.Ordinal
  | .m => Minute.Ordinal
  | .sss => Millisecond.Ordinal
  | .ss => Second.Ordinal
  | .s => Second.Ordinal
  | .ZZZZZ => Offset
  | .ZZZZ => Offset
  | .ZZZ => Offset
  | .Z => Offset
  | .z => String

private def formatPart (modifier : Modifier) (data : SingleFormatType modifier) : String :=
  match modifier with
  | .YYYY  => s!"{leftPad 4 '0' (toString data.toNat)}"
  | .YY    => s!"{leftPad 2 '0' (toString $ data.toNat % 100)}"
  | .MMMM  => unabbrevMonth data
  | .MMM   => abbrevMonth data
  | .MM    => s!"{leftPad 2 '0' (toString $ data.toNat)}"
  | .M     => s!"{data.toNat}"
  | .DD    => s!"{leftPad 2 '0' (toString $ data.toNat)}"
  | .D     => s!"{data.toNat}"
  | .d     => s!"{leftPad 2 ' ' $ toString data.toNat}"
  | .EEEE  => dayOfWeek data
  | .EEE   => abbrevDayOfWeek data
  | .hh    => s!"{leftPad 2 '0' (toString data.toNat)}"
  | .h     => s!"{data.toNat}"
  | .HH    => let hour := data.val % 12; if hour == 0 then "12" else s!"{leftPad 2 '0' $ toString hour}"
  | .H     => let hour := data.val % 12; if hour == 0 then "12" else s!"{hour}"
  | .AA    => match data with | .am => "AM" | .pm => "PM"
  | .aa    => match data with | .am => "am" | .pm => "pm"
  | .mm    => s!"{leftPad 2 '0' $ toString data.toNat}"
  | .m     => s!"{data.toNat}"
  | .sss    => s!"{leftPad 3 '0' $ toString data.toNat}"
  | .ss    => s!"{leftPad 2 '0' $ toString data.toNat}"
  | .s     => s!"{data.toNat}"
  | .ZZZZZ => data.toIsoString true
  | .ZZZZ  => data.toIsoString false
  | .ZZZ   => if data.second.val = 0 then "UTC" else data.toIsoString false
  | .Z     => if data.second.val = 0 then "Z" else data.toIsoString true
  | .z     => data

@[simp]
def FormatType (result: Type) : FormatString → Type
  | .modifier entry :: xs => (SingleFormatType entry) → (FormatType result xs)
  | .string _ :: xs => (FormatType result xs)
  | [] => result

private def position : Parsec Nat := λs => (ParseResult.success s (s.pos.byteIdx))

private def size (data : Parsec α) : Parsec (α × Nat) := do
  let st ← position
  let res ← data
  let en ← position
  pure (res, en-st)

private def transform (n: β → Option α) (p: Lean.Parsec β) : Lean.Parsec α := do
  let res ← p
  match n res with
  | some n => pure n
  | none => fail "cannot parse"

private def parseMonth : Lean.Parsec Month.Ordinal
  :=  (pstring "Jan" *> pure 1)
  <|> (pstring "Feb" *> pure 2)
  <|> (pstring "Mar" *> pure 3)
  <|> (pstring "Apr" *> pure 4)
  <|> (pstring "May" *> pure 5)
  <|> (pstring "Jun" *> pure 6)
  <|> (pstring "Jul" *> pure 7)
  <|> (pstring "Aug" *> pure 8)
  <|> (pstring "Sep" *> pure 9)
  <|> (pstring "Oct" *> pure 10)
  <|> (pstring "Nov" *> pure 11)
  <|> (pstring "Dec" *> pure 12)

private def parseMonthUnabbrev : Lean.Parsec Month.Ordinal
  :=  (pstring "January" *> pure 1)
  <|> (pstring "February" *> pure 2)
  <|> (pstring "March" *> pure 3)
  <|> (pstring "April" *> pure 4)
  <|> (pstring "May" *> pure 5)
  <|> (pstring "June" *> pure 6)
  <|> (pstring "July" *> pure 7)
  <|> (pstring "August" *> pure 8)
  <|> (pstring "September" *> pure 9)
  <|> (pstring "October" *> pure 10)
  <|> (pstring "November" *> pure 11)
  <|> (pstring "December" *> pure 12)

private def parseWeekday : Lean.Parsec Weekday
  :=  (pstring "Mon" *> pure Weekday.mon)
  <|> (pstring "Tue" *> pure Weekday.tue)
  <|> (pstring "Wed" *> pure Weekday.wed)
  <|> (pstring "Thu" *> pure Weekday.thu)
  <|> (pstring "Fri" *> pure Weekday.fri)
  <|> (pstring "Sat" *> pure Weekday.sat)
  <|> (pstring "Sun" *> pure Weekday.sun)

private def parseWeekdayUnnabrev : Lean.Parsec Weekday
  :=  (pstring "Monday" *> pure Weekday.mon)
  <|> (pstring "Tuesday" *> pure Weekday.tue)
  <|> (pstring "Wednesday" *> pure Weekday.wed)
  <|> (pstring "Thursday" *> pure Weekday.thu)
  <|> (pstring "Friday" *> pure Weekday.fri)
  <|> (pstring "Saturday" *> pure Weekday.sat)
  <|> (pstring "Sunday" *> pure Weekday.sun)

private def parserUpperHourMarker : Lean.Parsec HourMarker
  :=  (pstring "AM" *> pure HourMarker.am)
  <|> (pstring "PM" *> pure HourMarker.pm)

private def parserLowerHourMarker : Lean.Parsec HourMarker
  :=  (pstring "am" *> pure HourMarker.am)
  <|> (pstring "pm" *> pure HourMarker.pm)

private def threeDigit : Lean.Parsec Int := do
  let digit1 ← Lean.Parsec.digit
  let digit2 ← Lean.Parsec.digit
  let digit3 ← Lean.Parsec.digit
  return String.toNat! s!"{digit1}{digit2}{digit3}"

private def twoDigit : Lean.Parsec Int := do
  let digit1 ← Lean.Parsec.digit
  let digit2 ← Lean.Parsec.digit
  return String.toNat! s!"{digit1}{digit2}"

private def parseYearTwo : Lean.Parsec Int :=do
  let year ← twoDigit
  return if year < 70 then 2000 + year else 1900 + year

private def timeOffset (colon: Bool) : Lean.Parsec Offset := do
  let sign : Int ← (pstring "-" *> pure (-1)) <|> (pstring "+" *> pure 1)
  let hour ← twoDigit
  if colon then let _ ← pstring ":"
  let minutes ← twoDigit
  let res := (hour * 3600 + minutes * 60) * sign
  pure (Offset.ofSeconds (UnitVal.ofInt res))

private def timeOrUTC (utcString: String) (colon: Bool) : Lean.Parsec Offset :=
  (pstring utcString *> pure Offset.zero) <|> timeOffset colon

private def number : Lean.Parsec Nat := do
  String.toNat! <$> Lean.Parsec.many1Chars Lean.Parsec.digit

private def singleDigit : Lean.Parsec Nat := do
  let digit1 ← Lean.Parsec.digit
  return String.toNat! s!"{digit1}"

private def fourDigit : Lean.Parsec Int := do
  let digit1 ← Lean.Parsec.digit
  let digit2 ← Lean.Parsec.digit
  let digit3 ← Lean.Parsec.digit
  let digit4 ← Lean.Parsec.digit
  return String.toNat! s!"{digit1}{digit2}{digit3}{digit4}"

private def parserWithFormat : (typ: Modifier) → Lean.Parsec (SingleFormatType typ)
  | .YYYY => fourDigit
  | .YY => parseYearTwo
  | .MMMM => parseMonthUnabbrev
  | .MMM => parseMonth
  | .MM => transform Bounded.LE.ofInt twoDigit
  | .M => transform Bounded.LE.ofInt number
  | .DD => transform Bounded.LE.ofInt twoDigit
  | .D => transform Bounded.LE.ofInt number
  | .d => transform Bounded.LE.ofInt (Lean.Parsec.orElse twoDigit (λ_ => pchar ' ' *> (singleDigit)))
  | .EEEE => parseWeekdayUnnabrev
  | .EEE => parseWeekday
  | .hh => transform Bounded.LE.ofInt twoDigit
  | .h => transform Bounded.LE.ofInt number
  | .HH => do
    let res : Bounded.LE 1 13 ← transform Bounded.LE.ofInt twoDigit
    return (res.sub 1).expandTop (by decide)
  | .H => do
    let res : Bounded.LE 1 13 ← transform Bounded.LE.ofInt number
    return (res.sub 1).expandTop (by decide)
  | .AA => parserUpperHourMarker
  | .aa => parserLowerHourMarker
  | .mm => transform Bounded.LE.ofInt twoDigit
  | .m => transform Bounded.LE.ofInt number
  | .sss => transform Bounded.LE.ofInt threeDigit
  | .ss => transform Bounded.LE.ofInt twoDigit
  | .s => transform Bounded.LE.ofInt number
  | .ZZZZZ => timeOffset true
  | .ZZZZ => timeOffset false
  | .ZZZ => timeOrUTC "UTC" false
  | .Z => timeOrUTC "Z" true
  | .z => many1Chars (satisfy (λc => c == ' ' || c.isAlpha))

private structure DateBuilder where
  tzName : String := "Greenwich Mean Time"
  tz : Offset := Offset.zero
  year : Year.Offset := 0
  month : Month.Ordinal := 1
  day : Day.Ordinal := 1
  hour : Hour.Ordinal := 0
  minute : Minute.Ordinal := 0
  second : Second.Ordinal := 0
  millisecond : Millisecond.Ordinal := 0

private def DateBuilder.build (builder : DateBuilder) (aw : Awareness) : aw.type :=
  let build := DateTime.ofNaiveDateTime {
      date := Date.force builder.year builder.month builder.day
      time := Time.mk builder.hour builder.minute builder.second (.ofMillisecond builder.millisecond)
  }

  match aw with
  | .any =>
    let tz₁ := TimeZone.mk builder.tz builder.tzName
    ⟨tz₁, build tz₁⟩
  | .only tz =>
    build tz

private def addDataInDateTime (data : DateBuilder) (typ : Modifier) (value : SingleFormatType typ) : DateBuilder :=
  match typ with
  | .YYYY | .YY => { data with year := value }
  | .MMMM | .MMM | .MM | .M => { data with month := value }
  | .DD | .D | .d => { data with day := value }
  | .EEEE | .EEE => data
  | .hh | .h | .HH | .H => { data with hour := value }
  | .AA | .aa => { data with hour := HourMarker.toAbsolute! value data.hour }
  | .mm | .m => { data with minute := value }
  | .sss => { data with millisecond := value }
  | .ss | .s => { data with second := value }
  | .ZZZZZ | .ZZZZ | .ZZZ
  | .Z => { data with tz := value }
  | .z => { data with tzName := value }

private def formatParser (date : DateBuilder) : FormatPart → Lean.Parsec DateBuilder
  | .modifier mod => addDataInDateTime date mod <$> parserWithFormat mod
  | .string s => skipString s *> pure date

-- API

namespace Format

/--
Constructs a new `Format` specification for a date-time string. Modifiers can be combined to create
custom formats, such as %YYYY, MMMM, D".

### Supported Modifiers:
- `YYYY`: Four-digit year (e.g., 2024).
- `YY`: Two-digit year (e.g., 24 for 2024).
- `MMMM`: Full month name (e.g., January, February).
- `MMM`: Abbreviated month name (e.g., Jan, Feb).
- `MM`: Two-digit month (e.g., 01 for January).
- `M`: One or two-digit month (e.g., 1 for January, 10 for October).
- `DD`: Two-digit day of the month (e.g., 01, 02).
- `D`: One or two-digit day of the month (e.g., 1, 2).
- `d`: One or two-digit day of the month with left padding with spaces. (e.g., 1, 2).
- `EEEE`: Full name of the day of the week (e.g., Monday, Tuesday).
- `EEE`: Abbreviated day of the week (e.g., Mon, Tue).
- `hh`: Two-digit hour in 12-hour format (e.g., 01, 02).
- `h`: One or two-digit hour in 12-hour format (e.g., 1, 2).
- `HH`: Two-digit hour in 24-hour format (e.g., 13, 14).
- `H`: One or two-digit hour in 24-hour format (e.g., 1, 2).
- `AA`: Uppercase AM/PM indicator (e.g., AM, PM).
- `aa`: Lowercase am/pm indicator (e.g., am, pm).
- `mm`: Two-digit minute (e.g., 01, 02).
- `m`: One or two-digit minute (e.g., 1, 2).
- `sss`: Three-digit millisecond (e.g., 001, 002).
- `ss`: Two-digit second (e.g., 01, 02).
- `s`: One or two-digit second (e.g., 1, 2).
- `ZZZZZ`: Full timezone offset with hours and minutes (e.g., +03:00).
- `ZZZZ`: Timezone offset with hours and minutes, without the colon (e.g., +0300).
- `ZZZ`: Like `ZZZZ`, but displays "UTC" for UTC time.
- `Z`: Like `ZZZZZ`, but displays "Z" for UTC time.
- `z`: Timezone name (e.g., Brasilia Standard Time).

Example usage:
- `"YYYY-MM-DD HH:mm:ss ZZZZ"` → "2024-08-04 14:23:45 +0300"
-/
def spec (input : String) : Except String (Format tz) := do
  let string ← specParser.run input
  return ⟨string⟩

/--
Builds a new `Format` specification for a Date-time, panics if the input string results in an error.
-/
def spec! (input : String) : Format tz :=
  match specParser.run input with
  | .ok res => ⟨res⟩
  | .error res => panic! res

/--
Formats the date using the format into a String.
-/
def format (format : Format aw) (date : DateTime tz) : String :=
  let func :=
    match aw with
    | .any => formatPartWithDate date
    | .only tz => formatPartWithDate (date.convertTimeZone tz)

  format.string.map func
  |> String.join

/--
Formats the date using the format into a String.
-/
def formatBuilder (format : Format aw) : FormatType String format.string :=
  let rec go (data : String) : (format : FormatString) → FormatType String format
    | .modifier x :: xs => λres => go (data ++ formatPart x res) xs
    | .string x :: xs => go (data ++ x) xs
    | [] => data
  go "" format.string

/--
Parser for a ZonedDateTime.
-/
def parser (format : FormatString) (aw : Awareness) : Parsec (aw.type) :=
  let rec go (date : DateBuilder) (x : FormatString) : Parsec aw.type :=
    match x with
    | x :: xs => formatParser date x >>= (go · xs)
    | [] => pure (date.build aw)
  go {} format

/--
Parser for a format with a builder.
-/
def builderParser (format: FormatString) (func: FormatType α format) : Lean.Parsec α :=
  let rec go (format : FormatString) (func: FormatType α format) : Parsec α :=
    match format with
    | .modifier x :: xs => do
      let res ← parserWithFormat x
      go xs (func res)
    | .string s :: xs => skipString s *> (go xs func)
    | [] => pure func
  go format func

/--
Parses the input string into a `ZoneDateTime`
-/
def parse (format : Format aw) (input : String) : Except String aw.type :=
  (parser format.string aw).run input

/-
Parses the input string into a `ZoneDateTime`, panics if its wrong
-/
def parse! (format : Format aw) (input : String) : aw.type :=
  match parse format input with
  | .ok res => res
  | .error err => panic! err

/--
Parses and instead of using a builder to build a date, it uses a builder function instead.
-/
def parseBuilder (format : Format aw)  (builder : FormatType α format.string) (input : String) : Except String α :=
  (builderParser format.string builder).run input

/--
Parses and instead of using a builder to build a date, it uses a builder function instead.
-/
def parseBuilder! [Inhabited α] (format : Format aw)  (builder : FormatType α format.string) (input : String) : α :=
  match parseBuilder format builder input with
  | .ok res => res
  | .error err => panic! err

end Format
end Time
end Std
