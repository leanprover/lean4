/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Time.Time
public import Std.Time.Date
public import Std.Time.Zoned
public import Std.Time.Format
public import Std.Time.DateTime
public import Std.Time.Notation
public import Std.Time.Duration
public import Std.Time.Zoned.Database

public section

namespace Std.Time

/-!
# Time

The Lean API for date, time, and duration functionalities.

# Overview

This module of the standard library defines various concepts related to time, such as dates, times,
time zones and durations. These types are designed to be strongly-typed and to avoid problems with
conversion. It offers both unbounded and bounded variants to suit different use cases, like
adding days to a date or representing ordinal values.

# Date and Time Components

Date and time components are classified into different types based how you SHOULD use them. These
components are categorized as:

## Offset

Offsets represent unbounded shifts in specific date or time units. They are typically used in operations
like `date.addDays` where a `Day.Offset` is the parameter. Some offsets, such as `Month.Offset`, do not
correspond directly to a specific duration in seconds, as their value depends on the context (if
the year is leap or the size of the month). Offsets with a clear correspondent to seconds can be
converted because they use an internal type called `UnitVal`.

- Types with a correspondence to seconds:
  - `Day.Offset`
  - `Hour.Offset`
  - `Week.Offset`
  - `Millisecond.Offset`
  - `Nanosecond.Offset`
  - `Second.Offset`

- Types without a correspondence to seconds:
  - `Month.Offset`
  - `Year.Offset`

## Ordinal

Ordinal types represent specific bounded values in reference to another unit, e.g., `Day.Ordinal`
represents a day in a month, ranging from 1 to 31. Some ordinal types like `Hour.Ordinal` and `Second.Ordinal`,
allow for values beyond the normal range (e.g, 60 seconds) to accommodate special cases with leap seconds
like `23:59:60` that is valid in ISO 8601.

- Ordinal types:
  - `Day.Ordinal`: Ranges from 1 to 31.
  - `Day.Ordinal.OfYear`: Ranges from 1 to (365 or 366).
  - `Month.Ordinal`: Ranges from 1 to 12.
  - `WeekOfYear.Ordinal`: Ranges from 1 to 53.
  - `Hour.Ordinal`: Ranges from 0 to 23.
  - `Millisecond.Ordinal`: Ranges from 0 to 999.
  - `Minute.Ordinal`: Ranges from 0 to 59.
  - `Nanosecond.Ordinal`: Ranges from 0 to 999,999,999.
  - `Second.Ordinal`: Ranges from 0 to 60.
  - `Weekday`: That is an inductive type with all the seven days.

## Span

Span types are used as subcomponents of other types. They represent a range of values in the limits
of the parent type, e.g, `Nanosecond.Span` ranges from -999,999,999 to 999,999,999, as 1,000,000,000
nanoseconds corresponds to one second.

- Span types:
  - `Nanosecond.Span`: Ranges from -999,999,999 to 999,999,999.

# Date and Time Types

Dates and times are made up of different parts. An `Ordinal` is an absolute value, like a specific day in a month,
while an `Offset` is a shift forward or backward in time, used in arithmetic operations to add or subtract days, months or years.
Dates use components like `Year.Ordinal`, `Month.Ordinal`, and `Day.Ordinal` to ensure they represent
valid points in time.

Some types, like `Duration`, include a `Span` to represent ranges over other types, such as `Second.Offset`.
This type can have a fractional nanosecond part that can be negative or positive that is represented as a `Nanosecond.Span`.

## Date
These types provide precision down to the day level, useful for representing and manipulating dates.

- **`PlainDate`:** Represents a calendar date in the format `YYYY-MM-DD`.

## Time
These types offer precision down to the nanosecond level, useful for representing and manipulating time of day.

- **`PlainTime`**: Represents a time of day in the format `HH:mm:ss,sssssssss`.

## Date and time
Combines date and time into a single representation, useful for precise timestamps and scheduling.

- **`PlainDateTime`**: Represents both date and time in the format `YYYY-MM-DDTHH:mm:ss,sssssssss`.
- **`Timestamp`**: Represents a specific point in time with nanosecond precision. Its zero value corresponds
to the UNIX epoch. This type should be used when sending or receiving timestamps between systems.
- **`WallTime`**: Represents the local civil time shown by a clock in some timezone, stored as a `Duration`
since `1970-01-01T00:00:00` in local time. Unlike `Timestamp`, it is not tied to UTC; converting between
the two requires a timezone. It is convenient for performing arithmetic directly on local times without
first resolving to an absolute instant.

## Zoned date and times.
Combines date, time and time zones.

- **`DateTime`**: Is a way to represent date and time that includes `ZoneRules`, which consider
Daylight Saving Time (DST). If you want to use a specific time zone without worrying about DST, you can
use the `ofTimestampWithZone` function, which gives you a `DateTime` based only on that time zone,
without considering the zone rules, otherwise you can use `ofTimestamp` or `ofTimestampWithIdentifier`.

## Duration
Represents spans of time and the difference between two points in time.

- **`Duration`**: Represents the time span or difference between two `Timestamp`s values with nanosecond precision.

# Formats

Format strings are used to convert between `String` representations and date/time types, like `yyyy-MM-dd'T'HH:mm:ss.sssZ`.
The table below shows the available format specifiers. Repeating a pattern character may change the
text style, minimum width, or offset/fraction form, depending on the field.

The current Lean implementation follows Java's pattern language where practical, but it is not fully
locale-sensitive.

For numeric fields that accept both one- and two-letter forms, the single-letter form parses a
non-padded number and the two-letter form parses a zero-padded width of two.

The supported formats include:
- `G`: Represents the era, such as BCE (Before Common Era) or CE (Common Era).
  - `G`, `GG`, `GGG` (short): Displays the era in a short format (e.g., "CE").
  - `GGGG` (full): Displays the era in a full format (e.g., "Common Era").
  - `GGGGG` (narrow): Displays the era in a narrow format (e.g., "C").
- `y`: Represents the year of the era.
  - `y`: Represents the year in its full form, without a fixed length. It can handle years of any size, (e.g., "1", "2025", or "12345678").
  - `yy`: Displays the year in a two-digit format, showing the last two digits (e.g., "04" for 2004).
  - `yyyy`: Displays the year in a four-digit format (e.g., "2004").
  - `yyyy+`: Extended format for years with more than four digits.
- `Y`: Represents the week-based year (ISO-like behavior around year boundaries).
  - `Y`, `YYY`, `YYYY`: Displays the week-based year (e.g., "2017").
  - `YY`: Displays the last two digits of the week-based year (e.g., "17").
  - `YYYYY+`: Extended format for week-based years with more than four digits.
- `u`: Represents the year.
  - `u`: Represents the year in its full form, without a fixed length. It can handle years of any size, (e.g., "1", "2025", or "12345678").
  - `uu`: Two-digit year format, showing the last two digits (e.g., "04" for 2004).
  - `uuuu`: Displays the year in a four-digit format (e.g., "2004" or "-1000").
  - `uuuu+`: Extended format for handling years with more than four digits (e.g., "12345" or "-12345"). Useful for historical dates far into the past or future!
- `D`: Represents the day of the year.
- `M`: Represents the month of the year, displayed as either a number or text.
  - `M`, `MM`: Displays the month as a number, with `MM` zero-padded (e.g., "7" for July, "07" for July with padding).
  - `MMM`: Displays the abbreviated month name (e.g., "Jul").
  - `MMMM`: Displays the full month name (e.g., "July").
  - `MMMMM`: Displays the month in a narrow form (e.g., "J" for July).
- `L`: Represents the standalone month of the year.
  - Supports the same widths as `M`; in the current English data it formats the same values.
- `d`: Represents the day of the month.
- `Q`: Represents the quarter of the year.
  - `Q`, `QQ`: Displays the quarter as a number (e.g., "3", "03").
  - `QQQ` (short): Displays the quarter as an abbreviated text (e.g., "Q3").
  - `QQQQ` (full): Displays the full quarter text (e.g., "3rd quarter").
  - `QQQQQ` (narrow): Displays the quarter as a short number (e.g., "3").
- `q`: Represents the standalone quarter of the year.
  - Supports the same widths as `Q`; in the current English data it formats the same values.
- `w`: Represents the week of the week-based year, each week starts on Monday (e.g., "27").
- `W`: Represents the week of the month using the library's fixed Monday-first week model (e.g., "2").
- `E`: Represents the day of the week as text.
  - `E`, `EE`, `EEE`: Displays the abbreviated weekday name (e.g., "Tue").
  - `EEEE`: Displays the full day name (e.g., "Tuesday").
  - `EEEEE`: Displays the narrow day name (e.g., "T" for Tuesday).
  - `EEEEEE`: Displays the short two-letter weekday name (e.g., "Tu").
- `e`: Represents the weekday as number or text.
  - `e`, `ee`: Displays the weekday as a number, starting from 1 (Monday) to 7 (Sunday).
  - `eee`, `eeee`, `eeeee`: Displays the weekday as text (same format as `E`).
  - `eeeeee`: Displays the short two-letter weekday name (e.g., "Tu").
- `c`: Standalone weekday.
  - `c`: Displays the numeric weekday using the same Monday-to-Sunday numbering as `e`.
  - `ccc`, `cccc`, `ccccc`: Display standalone text (same values as `e` in the current English data).
  - `cccccc`: Displays the short two-letter weekday name (e.g., "Tu").
- `F`: Represents the occurrence of the weekday within the month (e.g., the 2nd Sunday formats as `2`).
- `a`: Represents the AM or PM designation of the day.
  - `a`, `aa`, `aaa`: Displays AM/PM (e.g., "PM").
  - `aaaa`: Displays the full form (e.g., "ante meridiem", "post meridiem").
  - `aaaaa`: Displays the narrow form (e.g., "a", "p").
- `b`: Represents the day period, extending AM/PM with noon and midnight (TR35 §4, supported in Java 16+). The `B` symbol (flexible day periods) is not supported.
  - `b`, `bb`, `bbb`: Displays a short form (e.g., "AM", "PM", "noon", "midnight").
  - `bbbb`: Displays a full form (e.g., "ante meridiem", "post meridiem", "noon", "midnight"); unlike `a`, the AM/PM spellings are lowercase here.
  - `bbbbb`: Displays a narrow form (e.g., "a", "p", "n", "mi").
- `h`: Represents the hour of the AM/PM clock (1-12) (e.g., "12").
  - `h`, `hh` are supported, matching Java.
- `K`: Represents the hour of the AM/PM clock (0-11) (e.g., "0").
  - `K`, `KK` are supported, matching Java.
- `k`: Represents the hour of the day in a 1-24 format (e.g., "24").
  - `k`, `kk` are supported, matching Java.
- `H`: Represents the hour of the day in a 0-23 format (e.g., "0").
  - `H`, `HH` are supported, matching Java.
- `m`: Represents the minute of the hour (e.g., "30").
  - `m`, `mm` are supported, matching Java.
- `s`: Represents the second of the minute (e.g., "55").
  - `s`, `ss` are supported, matching Java.
- `S`: Represents a fraction of a second, typically displayed as a decimal number (e.g., "978" for milliseconds).
  - One or more repetitions of the character truncates to the specified number of most-significant digits; it does not round.
- `A`: Represents the millisecond of the day (e.g., "1234").
  - One or more repetitions of the character indicates zero-padding to the specified number of characters (no truncation is applied).
- `n`: Represents the nanosecond of the second (e.g., "987654321"). This is a Lean/Java extension, not a TR35 field.
  - One or more repetitions of the character sets a minimum width via zero-padding; the value is not truncated.
- `N`: Represents the nanosecond of the day (e.g., "1234000000"). This is a Lean/Java extension, not a TR35 field.
  - One or more repetitions of the character sets a minimum width via zero-padding; the value is not truncated.
- `V`: Time zone ID.
  - `VV`: Displays the zone identifier/name.
  - Other counts are unsupported, matching Java.
- `z`: Represents the time zone name.
  - `z`, `zz`, `zzz`: Shows a short zone name; for offset-only zones this is the numeric offset (e.g., "+09:00"), for UTC this is "UTC", otherwise the abbreviation (e.g., "PST").
  - `zzzz`: Displays the full zone name; for offset-only zones this is the numeric offset (e.g., "+09:00"), for UTC this is "Coordinated Universal Time", otherwise the full zone name (e.g., "Pacific Standard Time").
- `v`: Generic time zone name.
  - `v`: In the current Lean timezone data this displays the stored abbreviation; for offset-only zones this is the numeric offset (e.g., "+09:00"), and for UTC it is normalized to "UTC".
  - `vvvv`: In the current Lean timezone data this displays the stored zone name/ID; for offset-only zones this is the numeric offset (e.g., "+09:00"), and for UTC it is normalized to "Coordinated Universal Time".
- `O`: Represents the localized zone offset in the format "GMT" followed by the time difference from UTC.
  - `O`: Displays the GMT offset in a short format (e.g., "GMT+8"), or "GMT" for UTC.
  - `OOOO`: Displays the full GMT offset with padded hour and minutes (e.g., "GMT+08:00"), or "GMT" for UTC.
- `X`: Represents the zone offset. It uses 'Z' for UTC and can represent any offset (positive or negative).
  - `X`: Displays hour and optional minute offset (e.g., "-08", "-0830", or "Z").
  - `XX`: Displays the hour and minute offset without a colon (e.g., "-0830").
  - `XXX`: Displays the hour and minute offset with a colon (e.g., "-08:30").
  - `XXXX`: Displays the hour and minute offset without a colon, with optional seconds (e.g., "-0830", "-083045").
  - `XXXXX`: Displays the hour and minute offset with a colon, with optional seconds (e.g., "-08:30", "-08:30:45").
- `x`: Represents the zone offset. Similar to `X`, but never displays `'Z'` for UTC.
  - `x`: Displays hour and optional minute offset (e.g., "+00", "+0530").
  - `xx`: Displays the hour and minute offset without a colon (e.g., "+0830").
  - `xxx`: Displays the hour and minute offset with a colon (e.g., "+08:30").
  - `xxxx`: Displays the hour and minute offset without a colon, with optional seconds (e.g., "+0830", "+083045").
  - `xxxxx`: Displays the hour and minute offset with a colon, with optional seconds (e.g., "+08:30", "+08:30:45").
- `Z`: Represents the zone offset in RFC/CLDR `Z` forms.
  - `Z`, `ZZ`, `ZZZ`: Displays hour and minute offset without colon, with optional seconds (e.g., "+0800", "+083045").
  - `ZZZZ`: Displays localized GMT form (e.g., "GMT+08:00").
  - `ZZZZZ`: Displays hour and minute offset with a colon and optional seconds, and uses `"Z"` for UTC (e.g., "Z", "+08:30", "+08:30:45").
# Runtime Parsing

- `DateTime.parse` parses common zoned date-time formats with explicit offsets, but does not resolve timezone identifiers like `[Europe/Paris]`.
- `DateTime.parseIO` resolves identifier-based inputs via the default timezone database.
- `DateTime.fromLeanDateTimeWithIdentifierString` is pure and does not perform timezone database resolution.
- `DateTime.fromLeanDateTimeWithIdentifierStringIO` resolves identifiers using the default timezone database.

# Macros

In order to help the user build dates easily, there are a lot of macros available for creating dates.
The `.sssssssss` can be omitted in most cases.


- **`date("uuuu-MM-dd")`**: Represents a date in the `uuuu-MM-dd` format, where `uuuu` refers to the year.
- **`time("HH:mm:ss.sssssssss")`**: Represents a time in the format `HH:mm:ss.sssssssss`, including optional support for nanoseconds.
- **`datetime("uuuu-MM-ddTHH:mm:ss.sssssssss")`**: Represents a datetime value in the `uuuu-MM-ddTHH:mm:ss.sssssssss` format, with optional nanoseconds.
- **`offset("+HH:mm")`**: Represents a timezone offset in the format `+HH:mm`, where `+` or `-` indicates the direction from UTC.
- **`timezone("NAME/ID ZZZ")`**: Specifies a timezone using a region-based name or ID, along with its associated offset.
- **`datespec("FORMAT")`**: Defines a compile-time date format based on the provided string.
- **`zoned("uuuu-MM-ddTHH:mm:ss.sssssssssZZZZZ")`**: Represents a `DateTime` with a fixed timezone and optional nanosecond precision.
- **`zoned("uuuu-MM-ddTHH:mm:ss.sssssssss[IDENTIFIER]")`**: Defines an `IO DateTime`, where the timezone identifier is dynamically retrieved from the default timezone database.
- **`zoned("uuuu-MM-ddTHH:mm:ss.sssssssss, timezone")`**: Represents an `IO DateTime`, using a specified `timezone` term and allowing optional nanoseconds.

-/

end Std.Time
