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
  PlainDateTime.ofTimestampAssumingUTC timestamp

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
Converts a `Timestamp` to a `PlainTime`
-/
@[inline]
def getTimeAssumingUTC (timestamp : Timestamp) : PlainTime :=
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

instance : HSub PlainDate PlainDate Duration where
  hSub x y := x.toTimestampAssumingUTC - y.toTimestampAssumingUTC

end PlainDate
namespace PlainDateTime

/--
Converts a `PlainDate` to a `Timestamp`
-/
@[inline]
def ofPlainDate (date : PlainDate) : PlainDateTime :=
  { date, time := PlainTime.midnight }

/--
Converts a `PlainDateTime` to a `PlainDate`
-/
@[inline]
def toPlainDate (pdt : PlainDateTime) : PlainDate :=
  pdt.date

/--
Converts a `PlainTime` to a `PlainDateTime`
-/
@[inline]
def ofPlainTime (time : PlainTime) : PlainDateTime :=
  { date := ⟨1, 1, 1, by decide⟩, time }

/--
Converts a `PlainDateTime` to a `PlainTime`
-/
@[inline]
def toPlainTime (pdt : PlainDateTime) : PlainTime :=
  pdt.time

instance : HSub PlainDateTime PlainDateTime Duration where
  hSub x y := x.toTimestampAssumingUTC - y.toTimestampAssumingUTC

end PlainDateTime
