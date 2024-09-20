/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Time.DateTime.Timestamp
import Std.Time.DateTime.PlainDateTime

namespace Std
namespace Time

namespace Timestamp

set_option linter.all true

/--
Converts a `PlainDateTime` to a `Timestamp`
-/
@[inline]
def ofPlainDateTimeAssumingUTC (pdt : PlainDateTime) : Timestamp :=
  pdt.toTimestampAssumingUTC

/--
Converts a `Timestamp` to a `PlainDateTime`
-/
@[inline]
def toPlainDateTimeAssumingUTC (timestamp : Timestamp) : PlainDateTime :=
  PlainDateTime.ofUTCTimestamp timestamp

/--
Converts a `PlainDate` to a `Timestamp`
-/
@[inline]
def ofPlainDateAssumingUTC (pd : PlainDate) : Timestamp :=
  let days := pd.toDaysSinceUNIXEpoch
  let secs := days.toSeconds
  Timestamp.ofSecondsSinceUnixEpoch secs

/--
Converts a `Timestamp` to a `PlainDate`
-/
@[inline]
def toPlainDateAssumingUTC (timestamp : Timestamp) : PlainDate :=
  let secs := timestamp.toSecondsSinceUnixEpoch
  let days := Day.Offset.ofSeconds secs
  PlainDate.ofDaysSinceUNIXEpoch days

/--
Converts a `PlainTime` to a `Timestamp`
-/
@[inline]
def ofPlainTime (pt : PlainTime) : Timestamp :=
  let nanos := pt.toNanoseconds
  Timestamp.ofNanosecondsSinceUnixEpoch nanos

/--
Converts a `Timestamp` to a `PlainTime`
-/
@[inline]
def toPlainTime (timestamp : Timestamp) : PlainTime :=
  let nanos := timestamp.toNanosecondsSinceUnixEpoch
  PlainTime.ofNanoseconds nanos

end Timestamp
namespace PlainDate

/--
Converts a `PlainDate` to a `Timestamp`
-/
@[inline]
def toTimestampAssumingUTC (pdt : PlainDate) : Timestamp :=
  Timestamp.ofPlainDateAssumingUTC pdt

/--
Calculates the duration between a given `PlainDate` and a specified date.

## Example

```lean
def example : Duration :=
  let startDate := date% 2023-1-1
  let endDate := date% 2023-3-15
  endDate.since startDate
```
-/
@[inline]
def since [ToTimestamp α] (date : PlainDate) (since : α) : Duration :=
  let date  := date.toTimestampAssumingUTC
  let since := ToTimestamp.toTimestamp since
  Std.Time.Duration.sub date.toDurationSinceUnixEpoch since.toDurationSinceUnixEpoch

instance : HSub PlainDate PlainDate Duration where
  hSub x y := x.toTimestampAssumingUTC - y.toTimestampAssumingUTC

end PlainDate
namespace PlainDateTime

/--
Converts a `PlainDate` to a `Timestamp`
-/
@[inline]
def ofPlainDate (pd : PlainDate) : PlainDateTime :=
  PlainDateTime.ofUTCTimestamp (Timestamp.ofPlainDateAssumingUTC pd)

/--
Converts a `PlainDateTime` to a `PlainDate`
-/
@[inline]
def toPlainDate (pdt : PlainDateTime) : PlainDate :=
  Timestamp.toPlainDateAssumingUTC pdt.toTimestampAssumingUTC

/--
Converts a `PlainTime` to a `PlainDateTime`
-/
@[inline]
def ofPlainTime (pt : PlainTime) : PlainDateTime :=
  PlainDateTime.ofUTCTimestamp (Timestamp.ofPlainTime pt)

/--
Converts a `PlainDateTime` to a `PlainTime`
-/
@[inline]
def toPlainTime (pdt : PlainDateTime) : PlainTime :=
  Timestamp.toPlainTime pdt.toTimestampAssumingUTC

instance : ToTimestamp PlainDateTime where
  toTimestamp := Timestamp.ofPlainDateTimeAssumingUTC

instance : ToTimestamp PlainDate where
  toTimestamp := Timestamp.ofPlainDateAssumingUTC

/--
Calculates the duration between a given `PlainDateTime` and a specified date.

## Example

```lean
example : Duration :=
  let startDate := date% 2023-1-1:05:10:20
  let endDate := date% 2023-3-15:05:10:20
  endDate.since startDate
```
-/
@[inline]
def since [ToTimestamp α] (date : PlainDateTime) (since : α) : Duration :=
  let date  := date.toTimestampAssumingUTC
  let since := ToTimestamp.toTimestamp since
  Std.Time.Duration.sub date.toDurationSinceUnixEpoch since.toDurationSinceUnixEpoch

instance : HSub PlainDateTime PlainDateTime Duration where
  hSub x y := x.toTimestampAssumingUTC - y.toTimestampAssumingUTC

end PlainDateTime
