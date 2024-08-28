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
def ofPlainDateTime (ldt : PlainDateTime) : Timestamp :=
  ldt.toPlainTimestamp

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
def ofPlainDate (ld : PlainDate) : Timestamp :=
  let days := ld.toDaysSinceUNIXEpoch
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
def ofPlainTime (lt : PlainTime) : Timestamp :=
  let nanos := lt.toNanoseconds
  Timestamp.ofNanosecondsSinceUnixEpoch nanos

/--
Converts a `Timestamp` to a `PlainTime`
-/
@[inline]
def toPlainTime (timestamp : Timestamp) : PlainTime :=
  let nanos := timestamp.toNanosecondsSinceUnixEpoch
  PlainTime.ofNanoseconds nanos

end Timestamp

namespace PlainDateTime

/--
Converts a `PlainDate` to a `Timestamp`
-/
@[inline]
def ofPlainDate (ld : PlainDate) : PlainDateTime :=
  PlainDateTime.ofUTCTimestamp (Timestamp.ofPlainDate ld)

/--
Converts a `PlainDateTime` to a `PlainDate`
-/
@[inline]
def toPlainDate (ldt : PlainDateTime) : PlainDate :=
  Timestamp.toPlainDate ldt.toPlainTimestamp

/--
Converts a `PlainTime` to a `PlainDateTime`
-/
@[inline]
def ofPlainTime (lt : PlainTime) : PlainDateTime :=
  PlainDateTime.ofUTCTimestamp (Timestamp.ofPlainTime lt)

/--
Converts a `PlainDateTime` to a `PlainTime`
-/
@[inline]
def toPlainTime (ldt : PlainDateTime) : PlainTime :=
  Timestamp.toPlainTime ldt.toPlainTimestamp

end PlainDateTime
