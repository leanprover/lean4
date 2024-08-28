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
def ofPlainDateTime (pdt : PlainDateTime) : Timestamp :=
  pdt.toTimestampAssumingUTC

/--
Converts a `Timestamp` to a `PlainDateTime`
-/
@[inline]
def toPlainDateTime (timestamp : Timestamp) : PlainDateTime :=
  PlainDateTime.ofUTCTimestamp timestamp

/--
Converts a `PlainDate` to a `Timestamp`
-/
@[inline]
def ofPlainDate (pd : PlainDate) : Timestamp :=
  let days := pd.toDaysSinceUNIXEpoch
  let secs := days.toSeconds
  Timestamp.ofSecondsSinceUnixEpoch secs

/--
Converts a `Timestamp` to a `PlainDate`
-/
@[inline]
def toPlainDate (timestamp : Timestamp) : PlainDate :=
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
def toTimestamp (pdt : PlainDate) : Timestamp :=
  Timestamp.ofPlainDate pdt

/--
Calculates the duration between a given `PlainDate` and a specified date.
-/
def since [ToTimestamp α] (date : PlainDate) (since : α) : Duration :=
  let date  := date.toTimestamp
  let since := ToTimestamp.toTimestamp since
  Std.Time.Duration.sub date.toDurationSinceUnixEpoch since.toDurationSinceUnixEpoch

end PlainDate
namespace PlainDateTime

/--
Converts a `PlainDate` to a `Timestamp`
-/
@[inline]
def ofPlainDate (pd : PlainDate) : PlainDateTime :=
  PlainDateTime.ofUTCTimestamp (Timestamp.ofPlainDate pd)

/--
Converts a `PlainDateTime` to a `PlainDate`
-/
@[inline]
def toPlainDate (pdt : PlainDateTime) : PlainDate :=
  Timestamp.toPlainDate pdt.toTimestampAssumingUTC

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
  toTimestamp := Timestamp.ofPlainDateTime

instance : ToTimestamp PlainDate where
  toTimestamp := Timestamp.ofPlainDate

/--
Converts a `PlainDateTime` to a `Timestamp`
-/
@[inline]
def toTimestamp (pdt : PlainDateTime) : Timestamp :=
  Timestamp.ofPlainDateTime pdt

/--
Calculates the duration between a given `PlainDateTime` and a specified date.
-/
def since [ToTimestamp α] (date : PlainDateTime) (since : α) : Duration :=
  let date  := date.toTimestamp
  let since := ToTimestamp.toTimestamp since
  Std.Time.Duration.sub date.toDurationSinceUnixEpoch since.toDurationSinceUnixEpoch

end PlainDateTime
