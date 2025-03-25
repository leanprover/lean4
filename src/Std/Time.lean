/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Time.Time
import Std.Time.Date
import Std.Time.Zoned
import Std.Time.Format
import Std.Time.DateTime
import Std.Time.Notation
import Std.Time.Duration
import Std.Time.Zoned.Database

namespace Std
namespace Time

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
  - `Weekday`: That is a inductive type with all the seven days.

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

## Zoned date and times.
Combines date, time and time zones.

- **`DateTime`**: Represents both date and time but with a time zone in the type constructor.
- **`ZonedDateTime`**: Is a way to represent date and time that includes `ZoneRules`, which consider
Daylight Saving Time (DST). This means it can handle local time changes throughout the year better
than a regular `DateTime`. If you want to use a specific time zone without worrying about DST, you can
use the `ofTimestampWithZone` function, which gives you a `ZonedDateTime` based only on that time zone,
without considering the zone rules, otherwise you can use `ofTimestamp` or `ofTimestampWithIdentifier`.

## Duration
Represents spans of time and the difference between two points in time.

- **`Duration`**: Represents the time span or difference between two `Timestamp`s values with nanosecond precision.

# Formats

Format strings are used to convert between `String` representations and date/time types, like `yyyy-MM-dd'T'HH:mm:ss.sssZ`.
The table below shows the available format specifiers. Some specifiers can be repeated to control truncation or offsets.
When a character is repeated `n` times, it usually truncates the value to `n` characters.

The `number` type format specifiers, such as `h` and `K`, are parsed based on the number of repetitions.
If the repetition count is one, the format allows values ranging from 1 up to the maximum capacity of
the respective data type.

The supported formats include:
- `G`: Represents the era, such as AD (Anno Domini) or BC (Before Christ).
  - `G`, `GG`, `GGG` (short): Displays the era in a short format (e.g., "AD").
  - `GGGG` (full): Displays the era in a full format (e.g., "Anno Domini").
  - `GGGGG` (narrow): Displays the era in a narrow format (e.g., "A").
- `y`: Represents the year of the era.
  - `y`: Represents the year in its full form, without a fixed length. It can handle years of any size, (e.g., "1", "2025", or "12345678").
  - `yy`: Displays the year in a two-digit format, showing the last two digits (e.g., "04" for 2004).
  - `yyyy`: Displays the year in a four-digit format (e.g., "2004").
  - `yyyy+`: Extended format for years with more than four digits.
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
- `d`: Represents the day of the month.
- `Q`: Represents the quarter of the year.
  - `Q`, `QQ`: Displays the quarter as a number (e.g., "3", "03").
  - `QQQ` (short): Displays the quarter as an abbreviated text (e.g., "Q3").
  - `QQQQ` (full): Displays the full quarter text (e.g., "3rd quarter").
  - `QQQQQ` (narrow): Displays the quarter as a short number (e.g., "3").
- `w`: Represents the week of the week-based year, each week starts on Monday (e.g., "27").
- `W`: Represents the week of the month, each week starts on Monday (e.g., "4").
- `E`: Represents the day of the week as text.
  - `E`, `EE`, `EEE`: Displays the abbreviated weekday name (e.g., "Tue").
  - `EEEE`: Displays the full day name (e.g., "Tuesday").
  - `EEEEE`: Displays the narrow day name (e.g., "T" for Tuesday).
- `e`: Represents the weekday as number or text.
  - `e`, `ee`: Displays the the as a number, starting from 1 (Monday) to 7 (Sunday).
  - `eee`, `eeee`, `eeeee`: Displays the weekday as text (same format as `E`).
- `F`: Represents the week of the month that the first week starts on the first day of the month (e.g., "3").
- `a`: Represents the AM or PM designation of the day.
  - `a`, `aa`, `aaa`: Displays AM or PM in a concise format (e.g., "PM").
  - `aaaa`: Displays the full AM/PM designation (e.g., "Post Meridium").
- `h`: Represents the hour of the AM/PM clock (1-12) (e.g., "12").
  - One or more repetitions of the character indicates the truncation of the value to the specified number of characters.
- `K`: Represents the hour of the AM/PM clock (0-11) (e.g., "0").
  - One or more repetitions of the character indicates the truncation of the value to the specified number of characters.
- `k`: Represents the hour of the day in a 1-24 format (e.g., "24").
  - One or more repetitions of the character indicates the truncation of the value to the specified number of characters.
- `H`: Represents the hour of the day in a 0-23 format (e.g., "0").
  - One or more repetitions of the character indicates the truncation of the value to the specified number of characters.
- `m`: Represents the minute of the hour (e.g., "30").
  - One or more repetitions of the character indicates the truncation of the value to the specified number of characters.
- `s`: Represents the second of the minute (e.g., "55").
  - One or more repetitions of the character indicates the truncation of the value to the specified number of characters.
- `S`: Represents a fraction of a second, typically displayed as a decimal number (e.g., "978" for milliseconds).
  - One or more repetitions of the character indicates the truncation of the value to the specified number of characters.
- `A`: Represents the millisecond of the day (e.g., "1234").
  - One or more repetitions of the character indicates the truncation of the value to the specified number of characters.
- `n`: Represents the nanosecond of the second (e.g., "987654321").
  - One or more repetitions of the character indicates the truncation of the value to the specified number of characters.
- `N`: Represents the nanosecond of the day (e.g., "1234000000").
  - One or more repetitions of the character indicates the truncation of the value to the specified number of characters.
- `VV`: Represents the time zone ID, which could be a city-based zone (e.g., "America/Los_Angeles"), a UTC marker (`"Z"`), or a specific offset (e.g., "-08:30").
  - One or more repetitions of the character indicates the truncation of the value to the specified number of characters.
- `z`: Represents the time zone name.
  - `z`, `zz`, `zzz`: Shows an abbreviated time zone name (e.g., "PST" for Pacific Standard Time).
  - `zzzz`: Displays the full time zone name (e.g., "Pacific Standard Time").
- `O`: Represents the localized zone offset in the format "GMT" followed by the time difference from UTC.
  - `O`: Displays the GMT offset in a simple format (e.g., "GMT+8").
  - `OOOO`: Displays the full GMT offset, including hours and minutes (e.g., "GMT+08:00").
- `X`: Represents the zone offset. It uses 'Z' for UTC and can represent any offset (positive or negative).
  - `X`: Displays the hour offset (e.g., "-08").
  - `XX`: Displays the hour and minute offset without a colon (e.g., "-0830").
  - `XXX`: Displays the hour and minute offset with a colon (e.g., "-08:30").
  - `XXXX`: Displays the hour, minute, and second offset without a colon (e.g., "-083045").
  - `XXXXX`: Displays the hour, minute, and second offset with a colon (e.g., "-08:30:45").
- `x`: Represents the zone offset. Similar to X, but does not display 'Z' for UTC and focuses only on positive offsets.
  - `x`: Displays the hour offset (e.g., "+08").
  - `xx`: Displays the hour and minute offset without a colon (e.g., "+0830").
  - `xxx`: Displays the hour and minute offset with a colon (e.g., "+08:30").
  - `xxxx`: Displays the hour, minute, and second offset without a colon (e.g., "+083045").
  - `xxxxx`: Displays the hour, minute, and second offset with a colon (e.g., "+08:30:45").
- `Z`: Always includes an hour and minute offset and may use 'Z' for UTC, providing clear differentiation between UTC and other time zones.
  - `Z`: Displays the hour and minute offset without a colon (e.g., "+0800").
  - `ZZ`: Displays "GMT" followed by the time offset (e.g., "GMT+08:00" or "Z").
  - `ZZZ`: Displays the full hour, minute, and second offset with a colon (e.g., "+08:30:45" or "Z").

# Macros

In order to help the user build dates easily, there are a lot of macros available for creating dates.
The `.sssssssss` can be ommited in most cases.


- **`date("uuuu-MM-dd")`**: Represents a date in the `uuuu-MM-dd` format, where `uuuu` refers to the year.
- **`time("HH:mm:ss.sssssssss")`**: Represents a time in the format `HH:mm:ss.sssssssss`, including optional support for nanoseconds.
- **`datetime("uuuu-MM-ddTHH:mm:ss.sssssssss")`**: Represents a datetime value in the `uuuu-MM-ddTHH:mm:ss.sssssssss` format, with optional nanoseconds.
- **`offset("+HH:mm")`**: Represents a timezone offset in the format `+HH:mm`, where `+` or `-` indicates the direction from UTC.
- **`timezone("NAME/ID ZZZ")`**: Specifies a timezone using a region-based name or ID, along with its associated offset.
- **`datespec("FORMAT")`**: Defines a compile-time date format based on the provided string.
- **`zoned("uuuu-MM-ddTHH:mm:ss.sssssssssZZZ")`**: Represents a `ZonedDateTime` with a fixed timezone and optional nanosecond precision.
- **`zoned("uuuu-MM-ddTHH:mm:ss.sssssssss[IDENTIFIER]")`**: Defines an `IO ZonedDateTime`, where the timezone identifier is dynamically retrieved from the default timezone database.
- **`zoned("uuuu-MM-ddTHH:mm:ss.sssssssss, timezone")`**: Represents an `IO ZonedDateTime`, using a specified `timezone` term and allowing optional nanoseconds.

-/
