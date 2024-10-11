/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Time.Notation.Spec
import Std.Time.Format.Basic
import Std.Time.Internal.Bounded

namespace Std
namespace Time
namespace Formats
open Internal

set_option linter.all true

/--
The ISO8601 format, which is always 24 or 27 characters long, used for representing date and time in
a standardized format. The format follows the pattern `yyyy-MM-dd:HH::mm:ss.SSSZ`.
-/
def iso8601 : Format .any := datespec("yyyy-MM-dd:HH::mm:ss.SSSZ")

/--
The americanDate format, which follows the pattern `MM-dd-yyyy`.
-/
def americanDate : Format .any := datespec("MM-dd-yyyy")

/--
The europeanDate format, which follows the pattern `dd-MM-yyyy`.
-/
def europeanDate : Format .any := datespec("dd-MM-yyyy")

/--
The time12Hour format, which follows the pattern `hh:mm:ss aa` for representing time
in a 12-hour clock format with an upper case AM/PM marker.
-/
def time12Hour : Format .any := datespec("hh:mm:ss aa")

/--
The Time24Hour format, which follows the pattern `HH:mm:ss:SSSSSSSSS` for representing time
in a 24-hour clock format.
-/
def time24Hour : Format .any := datespec("HH:mm:ss.SSSSSSSSS")

/--
The DateTimeZone24Hour format, which follows the pattern `yyyy-MM-dd:HH:mm:ss.SSSSSSSSS` for
representing date, time, and time zone.
-/
def dateTime24Hour : Format (.only .GMT) := datespec("yyyy-MM-dd:HH:mm:ss.SSSSSSSSS")

/--
The DateTimeWithZone format, which follows the pattern `yyyy-MM-dd:HH:mm:ss.SSSSSSSSSZZZ`
for representing date, time, and time zone.
-/
def dateTimeWithZone : Format .any := datespec("yyyy-MM-dd:HH:mm:ss.SSSSSSSSSZZZ")

/--
The Time24Hour format, which follows the pattern `HH:mm:ss` for representing time
in a 24-hour clock format. It uses the default value that can be parsed with the
notation of dates.
-/
def leanTime24Hour : Format .any := datespec("HH:mm:ss.SSSSSSSSS")

/--
The Time24Hour format, which follows the pattern `HH:mm:ss` for representing time
in a 24-hour clock format. It uses the default value that can be parsed with the
notation of dates.
-/
def leanTime24HourNoNanos : Format .any := datespec("HH:mm:ss")

/--
The DateTimeZone24Hour format, which follows the pattern `YYYY-MM-DD HH:mm:ss:sssssssss` for
representing date, time, and time zone. It uses the default value that can be parsed with the
notation of dates.
-/
def leanDateTime24Hour : Format (.only .GMT) := datespec("yyyy-MM-dd'T'HH:mm:ss.SSSSSSSSS")

/--
The DateTime24HourNoNanos format, which follows the pattern `YYYY-MM-DD HH:mm:ss` for
representing date, time, and time zone. It uses the default value that can be parsed with the
notation of dates.
-/
def leanDateTime24HourNoNanos : Format (.only .GMT) := datespec("yyyy-MM-dd'T'HH:mm:ss")

/--
The DateTimeWithZone format, which follows the pattern `YYYY-MM-DD HH:mm:ss.SSSSSSSSS`
for representing date, time, and time zone. It uses the default value that can be parsed with the
notation of dates.
-/
def leanDateTimeWithZone : Format .any := datespec("yyyy-MM-dd'T'HH:mm:ss.SSSSSSSSSZZZZZ")

/--
The DateTimeWithZoneNoNanos format, which follows the pattern `YYYY-MM-DD HH:mm:ssZZZZZ`
for representing date, time, and time zone. It uses the default value that can be parsed with the
notation of dates.
-/
def leanDateTimeWithZoneNoNanos : Format .any := datespec("yyyy-MM-dd'T'HH:mm:ssZZZZZ")

/--
The Lean Date format, which follows the pattern `yyyy-MM-DD`. It uses the default value that can be parsed with the
notation of dates.
-/
def leanDate : Format .any := datespec("yyyy-MM-dd")

/--
The SQLDate format, which follows the pattern `yyyy-MM-DD` and is commonly used
in SQL databases to represent dates.
-/
def sqlDate : Format .any := datespec("yyyy-MM-dd")

/--
The LongDateFormat, which follows the pattern `EEEE, MMMM D, yyyy HH:mm:ss` for
representing a full date and time with the day of the week and month name.
-/
def longDateFormat : Format (.only .GMT) := datespec("EEEE, MMMM D, yyyy HH:mm:ss")

/--
The AscTime format, which follows the pattern `EEE MMM d HH:mm:ss yyyy`. This format
is often used in older systems for logging and time-stamping events.
-/
def ascTime : Format (.only .GMT) := datespec("EEE MMM d HH:mm:ss yyyy")

/--
The RFC822 format, which follows the pattern `eee, dd MMM yyyy HH:mm:ss ZZZ`.
This format is used in email headers and HTTP headers.
-/
def rfc822 : Format .any := datespec("eee, dd MMM yyyy HH:mm:ss ZZZ")

/--
The RFC850 format, which follows the pattern `eee, dd-MMM-YY HH:mm:ss ZZZ`.
This format is an older standard for representing date and time in headers.
-/
def rfc850 : Format .any := datespec("eee, dd-MM-yyyy HH:mm:ss ZZZ")

end Formats

namespace TimeZone

/--
Parses a string into a `TimeZone` object. The input string must be in the format `"VV ZZZZZ"`.
-/
def fromTimeZone (input : String) : Except String TimeZone := do
  let spec : Format .any := datespec("VV ZZZZZ")
  spec.parseBuilder (λid off => some (TimeZone.mk off id "Unknown" false)) input

namespace Offset

/--
Parses a string representing an offset into an `Offset` object. The input string must follow the `"xxx"` format.
-/
def fromOffset (input : String) : Except String Offset := do
  let spec : Format .any := datespec("xxx")
  spec.parseBuilder some input

end Offset
end TimeZone

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
      | .y _ => some date.year
      | .MorL _ => some date.month
      | .d _ => some date.day
      | .E _ => some date.weekday
      | _ => none
    match res with
    | some res => res
    | none => "invalid time"

/--
Parses a date string in the American format (`MM/DD/yyyy`) and returns a `PlainDate`.
-/
def fromAmericanDateString (input : String) : Except String PlainDate := do
  Formats.americanDate.parseBuilder (fun m d y => PlainDate.ofYearMonthDay y m d) input

/--
Converts a Date in the American format (`MM/DD/yyyy`) into a `String`.
-/
def toAmericanDateString (input : PlainDate) : String :=
  Formats.americanDate.formatBuilder input.month input.day input.year

/--
Converts a Date in the SQL format (`YYYY-MM-DD`) into a `String`.
-/
def fromSQLDateString (input : String) : Except String PlainDate := do
  Formats.sqlDate.parseBuilder (PlainDate.ofYearMonthDay) input

/--
Converts a Date in the SQL format (`YYYY-MM-DD`) into a `String`.
-/
def toSQLDateString (input : PlainDate) : String :=
  Formats.sqlDate.formatBuilder input.year input.month input.day

/--
Parses a date string into a `PlainDate` object. The input string must be in the SQL date format.
-/
def fromLeanDateString (input : String) : Except String PlainDate := do
  Formats.sqlDate.parseBuilder (PlainDate.ofYearMonthDay) input

/--
Converts a Date in the Lean format (`YYYY-MM-DD`) into a `String` with the format `date% YYY-MM-DD`.
-/
def toLeanDateString (input : PlainDate) : String :=
  Formats.sqlDate.formatBuilder input.year input.month input.day

/--
Parses a `String` in the `AmericanDate` or `SQLDate` format and returns a `PlainDate`.
-/
def parse (input : String) : Except String PlainDate :=
  fromAmericanDateString input
  <|> fromSQLDateString input

instance : ToString PlainDate where
  toString := toLeanDateString

instance : Repr PlainDate where
  reprPrec data := Repr.addAppParen ("date(\"" ++ toLeanDateString data ++ "\")")

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
      | .H _ => some time.hour
      | .m _ => some time.minute
      | .n _ => some time.nano
      | .s _ => some time.second
      | _ => none
    match res with
    | some res => res
    | none => "invalid time"

/--
Parses a time string in the 24-hour format (`hh:mm:ss.sssssssss`) and returns a `PlainTime`.
-/
def fromTime24Hour (input : String) : Except String PlainTime :=
  Formats.time24Hour.parseBuilder (fun h m s n => some (PlainTime.ofHourMinuteSecondsNano h m s.snd n)) input

/--
Formats a `PlainTime` value into a 24-hour format string (`hh:mm:ss.sssssssss`).
-/
def toTime24Hour (input : PlainTime) : String :=
  Formats.time24Hour.formatBuilder input.hour input.minute input.second input.nano

/--
Parses a time string in the 24-hour format (`hh:mm:ss.sssssssss`) and returns a `PlainTime`.
-/
def fromLeanTime24Hour (input : String) : Except String PlainTime :=
  Formats.leanTime24Hour.parseBuilder (fun h m s n => some (PlainTime.ofHourMinuteSecondsNano h m s.snd n)) input
  <|> Formats.leanTime24HourNoNanos.parseBuilder (fun h m s => some (PlainTime.ofHourMinuteSecondsNano h m s.snd 0)) input

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
    let value ← Internal.Bounded.ofInt? h.val
    some <| PlainTime.ofHourMinuteSeconds (HourMarker.toAbsolute a value) m s.snd

  Formats.time12Hour.parseBuilder builder input

/--
Formats a `PlainTime` value into a 12-hour format string (`hh:mm:ss aa`).
-/
def toTime12Hour (input : PlainTime) : String :=
  Formats.time12Hour.formatBuilder (input.hour.emod 12 (by decide) |>.add 1) input.minute input.second (if input.hour.val ≥ 12 then HourMarker.pm else HourMarker.am)

/--
Parses a `String` in the `Time12Hour` or `Time24Hour` format and returns a `PlainTime`.
-/
def parse (input : String) : Except String PlainTime :=
  fromTime12Hour input
  <|> fromTime24Hour input

instance : ToString PlainTime where
  toString := toLeanTime24Hour

instance : Repr PlainTime where
  reprPrec data := Repr.addAppParen ("time(\"" ++ toLeanTime24Hour data ++ "\")")

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
  <|> Formats.leanDateTimeWithZoneNoNanos.parse input

/--
Formats a `DateTime` value into a simple date time with timezone string that can be parsed by the date% notationg.
-/
def toLeanDateTimeWithZoneString (zdt : ZonedDateTime) : String :=
  Formats.leanDateTimeWithZone.formatBuilder zdt.year zdt.month zdt.day zdt.hour zdt.minute zdt.snd.date.get.time.second zdt.nanosecond zdt.fst.offset

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
  reprPrec data := Repr.addAppParen ("zoned(\"" ++ toLeanDateTimeWithZoneString data ++ "\")")

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
      | .y _ => some date.date.year
      | .MorL _ => some date.date.month
      | .d _ => some date.date.day
      | .E _ => some date.date.weekday
      | .H _ => some date.time.hour
      | .m _ => some date.time.minute
      | .n _ => some date.time.nano
      | .S _ => some date.time.nano
      | .s _ => some date.time.second
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
  Formats.dateTime24Hour.formatBuilder pdt.year pdt.month pdt.day pdt.hour pdt.minute pdt.time.second pdt.nanosecond

/--
Parses a `String` in the `DateTime` format and returns a `PlainDateTime`.
-/
def fromLeanDateTimeString (input : String) : Except String PlainDateTime :=
  (Formats.leanDateTime24Hour.parse input <|> Formats.leanDateTime24HourNoNanos.parse input)
  |>.map DateTime.toPlainDateTime

/--
Formats a `PlainDateTime` value into a `DateTime` format string.
-/
def toLeanDateTimeString (pdt : PlainDateTime) : String :=
  Formats.leanDateTime24Hour.formatBuilder pdt.year pdt.month pdt.day pdt.hour pdt.minute pdt.time.second pdt.nanosecond

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
  reprPrec data := Repr.addAppParen ("datetime(\"" ++ toLeanDateTimeString data ++ "\")")

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

instance : Repr (DateTime tz) where
  reprPrec data := Repr.addAppParen (toLeanDateTimeWithZoneString data)

end DateTime
