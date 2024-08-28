/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Time.Zoned.DateTime
import Std.Time.Zoned.Database
import Std.Time.Zoned.ZoneRules
import Std.Time.Zoned.ZonedDateTime
import Std.Time.Zoned.ZonedDateTime
import Std.Time.Zoned.Database.Basic

namespace Std
namespace Time

namespace PlainDateTime

/--
Creaates a new `PlainDateTime` out of a `Timestamp` and a `TimeZone`.
-/
def ofTimestamp (stamp : Timestamp) (tz : TimeZone) : PlainDateTime :=
  let stamp := stamp.addSeconds tz.toSeconds
  PlainDateTime.ofUTCTimestamp stamp

/--
Get the current monotonic time.
-/
@[inline]
def now : IO PlainDateTime := do
  let tm ← Timestamp.now
  let tz ← TimeZone.getCurrentTimezone
  return PlainDateTime.ofTimestamp tm tz

end PlainDateTime

namespace DateTime

/--
Converts a `PlainDate` to a `DateTime`
-/
@[inline]
def ofPlainDate (pd : PlainDate) (tz : TimeZone) : DateTime tz :=
  DateTime.ofTimestamp (Timestamp.ofPlainDate pd) tz

/--
Converts a `DateTime` to a `PlainDate`
-/
@[inline]
def toPlainDate (dt : DateTime tz) : PlainDate :=
  Timestamp.toPlainDate dt.toTimestamp

/--
Converts a `PlainTime` to a `DateTime`
-/
@[inline]
def ofPlainTime (pt : PlainTime) (tz : TimeZone) : DateTime tz :=
  DateTime.ofTimestamp (Timestamp.ofPlainTime pt) tz

/--
Converts a `DateTime` to a `PlainTime`
-/
@[inline]
def toPlainTime (dt : DateTime tz) : PlainTime :=
  dt.date.get.time

/--
Calculates the duration between a given `DateTime` and a specified date.

## Example

```lean
example : Duration :=
  let startDate := date% 2023-1-1:05:10:20UTC
  let endDate := date% 2023-3-15:05:10:20UTC
  endDate.since startDate
```
-/
@[inline]
def since [ToTimestamp α] (date : DateTime tz) (since : α) : Duration :=
  let date  := date.toTimestamp
  let since := ToTimestamp.toTimestamp since
  Std.Time.Duration.sub date.toDurationSinceUnixEpoch since.toDurationSinceUnixEpoch

end DateTime
namespace ZonedDateTime

/--
Gets the current `DateTime`.
-/
@[inline]
def now : IO ZonedDateTime := do
  let date ← Timestamp.now
  let tz ← TimeZone.getCurrentTimezone
  return ofTimestamp date tz

/--
Converts a `PlainDate` to a `ZonedDateTime`
-/
@[inline]
def ofPlainDate (pd : PlainDate) (tz : TimeZone) : ZonedDateTime :=
  ⟨tz, DateTime.ofTimestamp (Timestamp.ofPlainDate pd) tz⟩

/--
Converts a `ZonedDateTime` to a `PlainDate`
-/
@[inline]
def toPlainDate (dt : ZonedDateTime) : PlainDate :=
  DateTime.toPlainDate dt.snd

/--
Converts a `PlainTime` to a `ZonedDateTime`
-/
@[inline]
def ofPlainTime (pt : PlainTime) (tz : TimeZone) : ZonedDateTime :=
  ⟨tz, DateTime.ofTimestamp (Timestamp.ofPlainTime pt) tz⟩

/--
Converts a `ZonedDateTime` to a `PlainTime`
-/
@[inline]
def toPlainTime (dt : ZonedDateTime) : PlainTime :=
  DateTime.toPlainTime dt.snd

/--
Calculates the duration between a given `ZonedDateTime` and a specified date.

## Example

```lean
def example : Duration :=
  let startDate := date% 2023-1-1:05:10:20UTC
  let endDate := date% 2023-3-15:05:10:20UTC
  endDate.since startDate
```
-/
@[inline]
def since [ToTimestamp α] (date : ZonedDateTime) (since : α) : Duration :=
  let date  := date.toTimestamp
  let since := ToTimestamp.toTimestamp since
  Std.Time.Duration.sub date.toDurationSinceUnixEpoch since.toDurationSinceUnixEpoch

end ZonedDateTime
