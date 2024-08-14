/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
import Std.Time.Time
import Std.Time.Date
import Std.Time.Zoned
import Std.Time.Format
import Std.Time.DateTime
import Std.Time.Notation
import Std.Time.Duration

namespace Std
namespace Time

set_option linter.all true

/-!
# Time

The Lean4 API for date, time, and duration functionalities, following the ISO standards.

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
  - `WeekOfYear.Offset`
  - `Millisecond.Offset`
  - `Nanosecond.Offset`
  - `Second.Offset`

- Types without a correspondence to seconds:
  - `Month.Offset`
  - `Year.Offset`

## Ordinal

Ordinal types represent specific bounded values in reference to another unit, e.g., `Day.Ordinal`
represents a day in a month, ranging from 1 to 31. Some ordinal types like `Hour.Ordinal` and `Second.Ordinal`,
allow for values beyond the normal range (e.g, 24 hours and 61 seconds) to accomodate special cases
with leap seconds like `24:00:00` that is valid in ISO 8601.

- Ordinal types:
  - `Day.Ordinal`: Ranges from 1 to 31.
  - `Day.Ordinal.OfYear`: Ranges from 1 to (365 or 366).
  - `Month.Ordinal`: Ranges from 1 to 12.
  - `WeekOfYear.Ordinal`: Ranges from 1 to 53.
  - `Hour.Ordinal`: Ranges from 0 to 24.
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

Dates and times are composed of these components. Dates are "absolute" value in contrast with Offsets
that are just shifts in dates and times. Types like `Date` are made using of components such as `Year.Offset`,
`Month.Ordinal`, and `Day.Ordinal`, with a proof of the date's validity.

## Date
These types provide precision down to the day level, useful for representing and manipulating dates.

- **`LocalDate`:** Represents a calendar date in the format `YYYY-MM-DD`.
- **`WeekDate`:** Uses the `YYYY-Www` format with week level precision.

## Time
These types offer precision down to the nanosecond level, useful for representing and manipulating time of day.

- **`LocalTime`**: Represents a time of day in the format `HH:mm:ss.SSSSSSSSS`.

## Date and time
Combines date and time into a single representation, useful for precise timestamps and scheduling.

- **`LocalDateTime`**: Represents both date and time in the format `YYYY-MM-DDTHH:mm:ss.SSSSSSSSS`.
- **`Timestamp`**: Represents a point in time with second-level precision. It starts on the UNIX
epoch and it should be used when you receive or need to send timestamps to another systems.

## Zoned date and times.
Combines date, time and time zones.

- **`DateTime`**: Represents both date and time but with a time zone in the type constructor.
- **`ZonedDateTime`**: An existential version of the `DateTime`.

## Duration
Represents spans of time and the difference between two points in time.

- **`Duration`**: Represents the time span or difference between two `Timestamp`s values with nanosecond precision.

# Formats

Format strings are used to convert between `String` representations and date/time types, e.g, `YYYY-MM-DD'T'hh:mm:ss.sssZ`.
The supported formats include:

- **Year:**
  - `YYYY`: Four-digit year (e.g., 2024)
  - `YY`: Two-digit year (e.g., 24 for 2024)
- **Month:**
  - `MMMM`: Full month name (e.g., January, February)
  - `MMM`: Abbreviated month name (e.g., Jan, Feb)
  - `MM`: Two-digit month (e.g., 01 for January)
  - `M`: One or two-digit month (e.g., 1 for January, 10 for October)
- **Day:**
  - `DD`: Two-digit day of the month (e.g., 01, 02)
  - `D`: One or two-digit day of the month (e.g., 1, 2)
  - `d`: One or two-digit day of the month with space padding (e.g., " 1", "12")
- **Day of Week:**
  - `EEEE`: Full name of the day of the week (e.g., Monday, Tuesday)
  - `EEE`: Abbreviated day of the week (e.g., Mon, Tue)
- **Hour:**
  - `hh`: Two-digit hour in 24-hour format (e.g., 13, 14)
  - `h`: One or two-digit hour in 24-hour format (e.g., 1, 2)
  - `HH`: Two-digit hour in 12-hour format (e.g., 01, 02)
  - `H`: One or two-digit hour in 12-hour format (e.g., 1, 2)
- **AM/PM Indicator:**
  - `AA`: Uppercase AM/PM (e.g., AM, PM)
  - `aa`: Lowercase am/pm (e.g., am, pm)
- **Minute:**
  - `mm`: Two-digit minute (e.g., 01, 02)
  - `m`: One or two-digit minute (e.g., 1, 2)
- **Second:**
  - `sss`: Three-digit milliseconds (e.g., 001, 202)
  - `ss`: Two-digit second (e.g., 01, 02)
  - `s`: One or two-digit second (e.g., 1, 2)
- **Timezone:**
  - `ZZZZZ`: Full timezone offset with hours and minutes (e.g., +03:00)
  - `ZZZZ`: Timezone offset without the colon (e.g., +0300)
  - `ZZZ`: Like `ZZZZ`, but with "UTC" for UTC
  - `Z`: Like `ZZZZZ`, but with "Z" for UTC
  - `z`: Timezone name (e.g., Brasilia Standard Time)

# Macros

In order to help the user build dates easily, there are a lot of macros available for creating dates.

- **`date% DD-MM-YYYY`**: Defines a date in the `DD-MM-YYYY` format.
- **`date% HH:mm:ss`**: Defines a time in the `HH:mm:ss` format.
- **`date% HH:mm:ss.sssssss`**: Defines a time in the `HH:mm:ss.sssssss` format, including fractional seconds.
- **`date% YYYY-MM-DD:HH:mm:ss`**: Defines a datetime in the `YYYY-MM-DD:HH:mm:ss` format.
- **`date% YYYY-MM-DDTHH:mm:ssZ`**: Defines a datetime with a timezone in the `YYYY-MM-DDTHH:mm:ssZ` format.
- **`offset% +HH:mm`**: Defines a timezone offset in the format `+HH:mm`.
- **`timezone% NAME/ID offset% +HH:mm`**: Defines a timezone with a name and an offset.
- **`date-spec% "format"`**: Defines a date specification format at compile time using the provided format string.
-/
