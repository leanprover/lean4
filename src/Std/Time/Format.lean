/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Time.Notation
import Std.Time.Format.Basic
import Std.Time.Internal.Bounded

namespace Std
namespace Time
namespace Formats

set_option linter.all true

/--
The ISO8601 format, which is always 24 or 27 characters long, used for representing date and time in
a standardized format. The format follows the pattern `YYYY-MM-DD'T'hh:mm:ss'Z'`.
-/
def iso8601 : Format .any := date-spec% "YYYY-MM-DD'T'hh:mm:ss.sssZ"

/--
The americanDate format, which follows the pattern `MM/DD/YYYY`.
-/
def americanDate : Format .any := date-spec% "MM-DD-YYYY"

/--
The europeanDate format, which follows the pattern `DD-MM-YYYY`.
-/
def europeanDate : Format .any := date-spec% "DD-MM-YYYY"

/--
The time12Hour format, which follows the pattern `HH:mm:ss AA` for representing time
in a 12-hour clock format with an upper case AM/PM marker.
-/
def time12Hour : Format .any := date-spec% "HH:mm:ss AA"

/--
The Time24Hour format, which follows the pattern `hh:mm:ss` for representing time
in a 24-hour clock format.
-/
def time24Hour : Format .any := date-spec% "hh:mm:ss:sssssssss"

/--
The DateTimeZone24Hour format, which follows the pattern `YYYY-MM-DD hh:mm:ss.sssssssss` for
representing date, time, and time zone.
-/
def dateTime24Hour : Format (.only .GMT) := date-spec% "YYYY-MM-DD:hh:mm:ss.sssssssss"

/--
The DateTimeWithZone format, which follows the pattern `YYYY-MM-DD hh:mm:ss.sssssssss`
for representing date, time, and time zone.
-/
def dateTimeWithZone : Format .any := date-spec% "YYYY-MM-DD:hh:mm:ss.sssssssssZZZ"

/--
The Time24Hour format, which follows the pattern `date% hh:mm:ss` for representing time
in a 24-hour clock format. It uses the default value that can be parsed with the
notation of dates.
-/
def leanTime24Hour : Format .any := date-spec% "'time% 'hh:mm:ss:sssssssss"

/--
The DateTimeZone24Hour format, which follows the pattern `date% YYYY-MM-DD hh:mm:ss:sssssssss` for
representing date, time, and time zone. It uses the default value that can be parsed with the
notation of dates.
-/
def leanDateTime24Hour : Format (.only .GMT) := date-spec% "'date% 'YYYY-MM-DD:hh:mm:ss:sssssssss"

/--
The DateTimeWithZone format, which follows the pattern `date% YYYY-MM-DD hh:mm:ss:sssssssss`
for representing date, time, and time zone. It uses the default value that can be parsed with the
notation of dates.
-/
def leanDateTimeWithZone : Format .any := date-spec% "'date% 'YYYY-MM-DD:hh:mm:ss:sssssssssZZZZZ"

/--
The Lean Date format, which follows the pattern `date% YYYY-MM-DD`. It uses the default value that can be parsed with the
notation of dates.
-/
def leanDate : Format .any := date-spec% "'date% 'YYYY-MM-DD"

/--
The SQLDate format, which follows the pattern `YYYY-MM-DD` and is commonly used
in SQL databases to represent dates.
-/
def sqlDate : Format .any := date-spec% "YYYY-MM-DD"

/--
The LongDateFormat, which follows the pattern `EEEE, MMMM D, YYYY hh:mm:ss` for
representing a full date and time with the day of the week and month name.
-/
def longDateFormat : Format (.only .GMT) := date-spec% "EEEE, MMMM D, YYYY hh:mm:ss"

/--
The AscTime format, which follows the pattern `EEE MMM d hh:mm:ss YYYY`. This format
is often used in older systems for logging and time-stamping events.
-/
def ascTime : Format (.only .GMT) := date-spec% "EEE MMM d hh:mm:ss YYYY"

/--
The RFC822 format, which follows the pattern `EEE, DD MMM YYYY hh:mm:ss ZZZ`.
This format is used in email headers and HTTP headers.
-/
def rfc822 : Format .any := date-spec% "EEE, DD MMM YYYY hh:mm:ss ZZZ"

/--
The RFC850 format, which follows the pattern `EEEE, DD-MMM-YY hh:mm:ss ZZZ`.
This format is an older standard for representing date and time in headers.
-/
def rfc850 : Format .any := date-spec% "EEEE, DD-MMM-YY hh:mm:ss ZZZ"

end Formats

namespace PlainDate

/--
Formats a `PlainDate` using a specific format.
-/
def format (date : PlainDate) (format : String) : String :=
  let format : Except String (Format .any) := Format.spec format
  match format with
  | .error err => s!"error: {err}"
  | .ok res =>
    let res := res.formatGeneric fun
      | .YYYY | .YY => some date.year
      | .MMMM | .MMM | .MM | .M => some date.month
      | .DD | .D | .d => some date.day
      | .EEEE | .EEE => some date.weekday
      | _ => none
    match res with
    | some res => res
    | none => "invalid time"

/--
Parses a date string in the American format (`MM/DD/YYYY`) and returns a `PlainDate`.
-/
def fromAmericanDateString (input : String) : Except String PlainDate := do
  Formats.americanDate.parseBuilder (λm d y => PlainDate.ofYearMonthDay y m d) input

/--
Converts a Date in the American format (`MM/DD/YYYY`) into a `String`.
-/
def toAmericanDateString (input : PlainDate) : String :=
  Formats.americanDate.formatBuilder input.month input.day input.year

/--
Converts a Date in the SQL format (`YYYY-MM-DD`) into a `String`.
-/
def fromSQLDateString (input : String) : Except String PlainDate := do
  Formats.sqlDate.parseBuilder (λy m d => PlainDate.ofYearMonthDay y m d) input

/--
Converts a Date in the SQL format (`YYYY-MM-DD`) into a `String`.
-/
def toSQLDateString (input : PlainDate) : String :=
  Formats.sqlDate.formatBuilder input.year input.month input.day

/--
Converts a Date in the Lean format (`YYYY-MM-DD`) into a `String` with the format `date% YYY-MM-DD`.
-/
def toLeanDateString (input : PlainDate) : String :=
  Formats.leanDate.formatBuilder input.year input.month input.day

/--
Parses a `String` in the `AmericanDate` or `SQLDate` format and returns a `PlainDate`.
-/
def parse (input : String) : Except String PlainDate :=
  fromAmericanDateString input
  <|> fromSQLDateString input

instance : ToString PlainDate where
  toString := toSQLDateString

instance : Repr PlainDate where
  reprPrec data := Repr.addAppParen (toLeanDateString data)

end PlainDate

namespace PlainTime

/--
Formats a `PlainTime` using a specific format.
-/
def format (time : PlainTime) (format : String) : String :=
  let format : Except String (Format .any) := Format.spec format
  match format with
  | .error err => s!"error: {err}"
  | .ok res =>
    let res := res.formatGeneric fun
      | .HH | .H => some time.hour
      | .mm | .m => some time.minute
      | .sss => some (Internal.Bounded.LE.ofNat 0 (by decide))
      | .ss | .s => some time.second
      | _ => none
    match res with
    | some res => res
    | none => "invalid time"

/--
Parses a time string in the 24-hour format (`hh:mm:ss.sssssssss`) and returns a `PlainTime`.
-/
def fromTime24Hour (input : String) : Except String PlainTime :=
  Formats.time24Hour.parseBuilder (λh m s n => PlainTime.ofHourMinuteSecondsNano? h.snd m s.snd n) input

/--
Formats a `PlainTime` value into a 24-hour format string (`hh:mm:ss.sssssssss`).
-/
def toTime24Hour (input : PlainTime) : String :=
  Formats.time24Hour.formatBuilder input.hour input.minute input.second input.nano

/--
Parses a time string in the 24-hour format (`hh:mm:ss.sssssssss`) and returns a `PlainTime`.
-/
def fromLeanTime24Hour (input : String) : Except String PlainTime :=
  Formats.leanTime24Hour.parseBuilder (λh m s n => PlainTime.ofHourMinuteSecondsNano? h.snd m s.snd n) input

/--
Formats a `PlainTime` value into a 24-hour format string (`hh:mm:ss.sssssssss`).
-/
def toLeanTime24Hour (input : PlainTime) : String :=
  Formats.leanTime24Hour.formatBuilder input.hour input.minute input.second input.nano

/--
Parses a time string in the 12-hour format (`hh:mm:ss aa`) and returns a `PlainTime`.
-/
def fromTime12Hour (input : String) : Except String PlainTime := do
  let builder h m s a : Option PlainTime := do
    let value ← Internal.Bounded.ofInt? h.snd.val
    PlainTime.ofHourMinuteSeconds? (leap₂ := false) (HourMarker.toAbsolute a value) m s.snd

  Formats.time12Hour.parseBuilder builder input

/--
Formats a `PlainTime` value into a 12-hour format string (`hh:mm:ss aa`).
-/
def toTime12Hour (input : PlainTime) : String :=
  Formats.time12Hour.formatBuilder input.hour input.minute input.second (if input.hour.snd.val ≥ 12 then HourMarker.pm else HourMarker.am)

/--
Parses a `String` in the `Time12Hour` or `Time24Hour` format and returns a `PlainTime`.
-/
def parse (input : String) : Except String PlainTime :=
  fromTime12Hour input
  <|> fromTime24Hour input

instance : ToString PlainTime where
  toString := toLeanTime24Hour

instance : Repr PlainTime where
  reprPrec data := Repr.addAppParen (toString data)

end PlainTime

namespace ZonedDateTime


/--
Formats a `ZonedDateTime` using a specific format.
-/
def format (data: ZonedDateTime) (format : String) : String :=
  let format : Except String (Format .any) := Format.spec format
  match format with
  | .error err => s!"error: {err}"
  | .ok res => res.format data.snd

/--
Parses a `String` in the `ISO8601` format and returns a `ZonedDateTime`.
-/
def fromISO8601String (input : String) : Except String ZonedDateTime :=
  Formats.iso8601.parse input

/--
Formats a `ZonedDateTime` value into an ISO8601 string.
-/
def toISO8601String (date : ZonedDateTime) : String :=
  Formats.iso8601.format date.snd

/--
Parses a `String` in the `RFC822` format and returns a `ZonedDateTime`.
-/
def fromRFC822String (input : String) : Except String ZonedDateTime :=
  Formats.rfc822.parse input

/--
Formats a `ZonedDateTime` value into an RFC822 format string.
-/
def toRFC822String (date : ZonedDateTime) : String :=
  Formats.rfc822.format date.snd

/--
Parses a `String` in the `RFC850` format and returns a `ZonedDateTime`.
-/
def fromRFC850String (input : String) : Except String ZonedDateTime :=
  Formats.rfc850.parse input

/--
Formats a `ZonedDateTime` value into an RFC850 format string.
-/
def toRFC850String (date : ZonedDateTime) : String :=
  Formats.rfc850.format date.snd

/--
Parses a `String` in the `DateTimeWithZone` format and returns a `DateTime` object in the GMT time zone.
-/
def fromDateTimeWithZoneString (input : String) : Except String ZonedDateTime :=
  Formats.dateTimeWithZone.parse input

/--
Formats a `DateTime` value into a simple date time with timezone string.
-/
def toDateTimeWithZoneString (pdt : ZonedDateTime) : String :=
  Formats.dateTimeWithZone.format pdt.snd

/--
Parses a `String` in the `DateTimeWithZone` format and returns a `DateTime` object in the GMT time zone.
-/
def fromLeanDateTimeWithZoneString (input : String) : Except String ZonedDateTime :=
  Formats.leanDateTimeWithZone.parse input

/--
Formats a `DateTime` value into a simple date time with timezone string that can be parsed by the date% notationg.
-/
def toLeanDateTimeWithZoneString (pdt : ZonedDateTime) : String :=
  Formats.leanDateTimeWithZone.format pdt.snd

/--
Parses a `String` in the `ISO8601`, `RFC822` or `RFC850` format and returns a `ZonedDateTime`.
-/
def parse (input : String) : Except String ZonedDateTime :=
  fromISO8601String input
  <|> fromRFC822String input
  <|> fromRFC850String input

instance : ToString ZonedDateTime where
  toString := toLeanDateTimeWithZoneString

instance : Repr ZonedDateTime where
  reprPrec data := Repr.addAppParen (toString data)

end ZonedDateTime

namespace PlainDateTime

/--
Formats a `PlainDateTime` using a specific format.
-/
def format (date : PlainDateTime) (format : String) : String :=
  let format : Except String (Format .any) := Format.spec format
  match format with
  | .error err => s!"error: {err}"
  | .ok res =>
    let res := res.formatGeneric fun
      | .YYYY | .YY => some date.year
      | .MMMM | .MMM | .MM | .M => some date.month
      | .DD | .D | .d => some date.day
      | .EEEE | .EEE => some date.date.weekday
      | .HH | .H => some date.time.hour
      | .hh | .h => some date.time.hour
      | .aa | .AA => some (if date.time.hour.snd.val > 12 then HourMarker.pm else HourMarker.am)
      | .mm | .m => some date.time.minute
      | .sssssssss => some date.time.nano
      | .sss => some date.time.nano.toMillisecond
      | .ss | .s => some date.time.second
      | _ => none
    match res with
    | some res => res
    | none => "invalid time"

/--
Parses a `String` in the `AscTime` format and returns a `PlainDateTime` object in the GMT time zone.
-/
def fromAscTimeString (input : String) : Except String PlainDateTime :=
  Formats.ascTime.parse input
  |>.map DateTime.toPlainDateTime

/--
Formats a `PlainDateTime` value into an AscTime format string.
-/
def toAscTimeString (pdt : PlainDateTime) : String :=
  Formats.ascTime.format (DateTime.ofPlainDateTimeAssumingUTC pdt .UTC)

/--
Parses a `String` in the `LongDateFormat` and returns a `PlainDateTime` object in the GMT time zone.
-/
def fromLongDateFormatString (input : String) : Except String PlainDateTime :=
  Formats.longDateFormat.parse input
  |>.map DateTime.toPlainDateTime

/--
Formats a `PlainDateTime` value into a LongDateFormat string.
-/
def toLongDateFormatString (pdt : PlainDateTime) : String :=
  Formats.longDateFormat.format (DateTime.ofPlainDateTimeAssumingUTC pdt .UTC)

/--
Parses a `String` in the `DateTime` format and returns a `PlainDateTime`.
-/
def fromDateTimeString (input : String) : Except String PlainDateTime :=
  Formats.dateTime24Hour.parse input
  |>.map DateTime.toPlainDateTime

/--
Formats a `PlainDateTime` value into a `DateTime` format string.
-/
def toDateTimeString (pdt : PlainDateTime) : String :=
  Formats.dateTime24Hour.format (DateTime.ofPlainDateTimeAssumingUTC pdt .UTC)

/--
Parses a `String` in the `DateTime` format and returns a `PlainDateTime`.
-/
def fromLeanDateTimeString (input : String) : Except String PlainDateTime :=
  Formats.leanDateTime24Hour.parse input
  |>.map DateTime.toPlainDateTime

/--
Formats a `PlainDateTime` value into a `DateTime` format string.
-/
def toLeanDateTimeString (pdt : PlainDateTime) : String :=
  Formats.leanDateTime24Hour.format (DateTime.ofPlainDateTimeAssumingUTC pdt .UTC)

/--
Parses a `String` in the `AscTime` or `LongDate` format and returns a `PlainDateTime`.
-/
def parse (date : String) : Except String PlainDateTime :=
  fromAscTimeString date
  <|> fromLongDateFormatString date
  <|> fromDateTimeString date

instance : ToString PlainDateTime where
  toString := toLeanDateTimeString

instance : Repr PlainDateTime where
  reprPrec data := Repr.addAppParen (toString data)

end PlainDateTime

namespace DateTime

/--
Formats a `DateTime` using a specific format.
-/
def format (data: DateTime tz) (format : String) : String :=
  let format : Except String (Format .any) := Format.spec format
  match format with
  | .error err => s!"error: {err}"
  | .ok res => res.format data

/--
Parses a `String` in the `AscTime` format and returns a `DateTime` object in the GMT time zone.
-/
def fromAscTimeString (input : String) : Except String (DateTime .GMT) :=
  Formats.ascTime.parse input

/--
Formats a `DateTime` value into an AscTime format string.
-/
def toAscTimeString (datetime : DateTime .GMT) : String :=
  Formats.ascTime.format datetime

/--
Parses a `String` in the `LongDateFormat` and returns a `DateTime` object in the GMT time zone.
-/
def fromLongDateFormatString (input : String) : Except String (DateTime .GMT) :=
  Formats.longDateFormat.parse input

/--
Formats a `DateTime` value into a LongDateFormat string.
-/
def toLongDateFormatString (datetime : DateTime .GMT) : String :=
  Formats.longDateFormat.format datetime

/--
Formats a `DateTime` value into an ISO8601 string.
-/
def toISO8601String (date : DateTime tz) : String :=
  Formats.iso8601.format date

/--
Formats a `DateTime` value into an RFC822 format string.
-/
def toRFC822String (date : DateTime tz) : String :=
  Formats.rfc822.format date

/--
Formats a `DateTime` value into an RFC850 format string.
-/
def toRFC850String (date : DateTime tz) : String :=
  Formats.rfc850.format date

/--
Formats a `DateTime` value into a `DateTimeWithZone` format string.
-/
def toDateTimeWithZoneString (pdt : DateTime tz) : String :=
  Formats.dateTimeWithZone.format pdt

/--
Formats a `DateTime` value into a `DateTimeWithZone` format string that can be parsed by `date%`.
-/
def toLeanDateTimeWithZoneString (pdt : DateTime tz) : String :=
  Formats.leanDateTimeWithZone.format pdt

/--
Parses a `String` in the `AscTime` or `LongDate` format and returns a `DateTime`.
-/
def parse (date : String) : Except String (DateTime .GMT) :=
  fromAscTimeString date
  <|> fromLongDateFormatString date

instance : ToString (DateTime tz) where
  toString := toLeanDateTimeWithZoneString

instance : Repr (DateTime tz) where
  reprPrec data := Repr.addAppParen (toString data)

end DateTime
